/*!
Goal: We need to mark every expression that we actually care about computing
These expressions are those that are used as an access index,
Anything that stores to a variable used as an access index,
and anything that affects control flow either for the access index itself
or for any store to a variable.
We can skip all other expressions
1. Visit all expressions and compute their dependencies.
2. For each `Store` statement, we mark the variables that are used to compute its value.
3. For any control flow statement, mark the variables that impact the control flow.
4. We also mark whether the statement contains an Access Index, and, if it does, the expression that is used as the index.
*/
use super::*;
pub(super) struct VarVisitorResult {
    /// Maps each expression to the set of expressions that it references.
    pub(super) subexpr_map:
        FastHashMap<Handle<Expression>, std::cell::RefCell<FastHashSet<TrackedVar>>>,

    /// The set of expressions that contain any access expression as a sub expression.
    pub(super) exprs_with_accesses: FastHashSet<Handle<Expression>>,

    /// The set of local variables, global variables, and function arguments that are used as indices of any access expression.
    pub(super) index_access_dependencies: FastHashSet<TrackedVar>,
}

/// Visits the expressions in the arena, and computes the read set, access indices, and indexed into set.
impl<'a> VarVisitor<'a> {
    pub(super) fn visit_arena(
        arena: &'a Arena<Expression>,
        lvar_arena: &'a Arena<LocalVariable>,
        gvar_arena: &'a Arena<GlobalVariable>,
        gexpr_arena: &'a Arena<Expression>,
        is_indexable: Box<dyn Fn(Handle<Expression>) -> bool + 'a>,
    ) -> Result<VarVisitorResult, VisitorError> {
        // Okay, we need to make a VarVisitor here.
        let dependency_map = FastHashMap::with_capacity_and_hasher(arena.len(), Default::default());
        let access_indices = FastHashSet::default();
        let indexed_into = FastHashSet::default();

        let mut visitor = Self::new(
            dependency_map,
            access_indices,
            indexed_into,
            lvar_arena,
            gvar_arena,
            gexpr_arena,
            is_indexable,
        );

        // Now, we go backwards through the expressions in the arena and visit them.
        // Going backwards here lets us call fewer visits, as our visitor will visit expressions
        for (handle, _) in arena.iter().rev() {
            visitor.visit(handle, arena)?;
        }

        Ok(VarVisitorResult {
            subexpr_map: visitor.subexpr_map,
            exprs_with_accesses: visitor.exprs_with_accesses,
            index_access_dependencies: visitor.index_access_dependencies,
        })
    }
}

/// Compute the set of variables that an expression (including its sub expressions) references
pub(super) struct VarVisitor<'a> {
    /// A map of expressions to the sub expressions they reference
    subexpr_map: FastHashMap<Handle<Expression>, std::cell::RefCell<FastHashSet<TrackedVar>>>,
    /// The same map, but where the keys are

    /// The set of local variables, global variables, and function arguments that are used as indices of any access expression
    index_access_dependencies: FastHashSet<TrackedVar>,

    /// The set of expressions that contain an index as a sub expression.
    exprs_with_accesses: FastHashSet<Handle<Expression>>,
    // The set of expressions that are used as indices of an access expression.
    // The set of expressions that are indices
    expr_stack: Vec<Handle<Expression>>,
    lvar_arena: &'a Arena<LocalVariable>,
    gvar_arena: &'a Arena<GlobalVariable>,
    gexpr_arena: &'a Arena<Expression>,

    // Two fields that are privately initialized and used only by the visitor.
    active_expr: Option<Handle<Expression>>,
    is_indexable: Box<dyn Fn(Handle<Expression>) -> bool + 'a>,
    in_global_context: bool,
}

impl<'a> VarVisitor<'a> {
    fn new(
        dependency_map: FastHashMap<
            Handle<Expression>,
            std::cell::RefCell<FastHashSet<TrackedVar>>,
        >,
        access_indices: FastHashSet<TrackedVar>,
        indexed_into: FastHashSet<Handle<Expression>>,
        lvar_arena: &'a Arena<LocalVariable>,
        gvar_arena: &'a Arena<GlobalVariable>,
        gexpr_arena: &'a Arena<Expression>,
        is_indexable: Box<dyn Fn(Handle<Expression>) -> bool + 'a>,
    ) -> Self {
        Self {
            active_expr: None,
            expr_stack: Vec::new(),
            lvar_arena,
            gvar_arena,
            gexpr_arena,
            subexpr_map: dependency_map,
            index_access_dependencies: access_indices,
            exprs_with_accesses: indexed_into,
            is_indexable,
            in_global_context: false,
        }
    }

    /// Add `base` to the read set for the active expression.
    ///
    /// NB: `self` is not borrowed mutably, as the active expression set is hidden behind a RefCell.
    ///
    /// # Errors
    /// [`VisitorError::BadHandle`] if the active expression is not in the handle map, or if its corresponding entry
    /// is already borrowed mutably.
    ///
    /// [`VisitorError::BadHandle`]: crate::VisitorError::BadHandle
    fn add_to_active(&self, base: TrackedVar) -> Result<(), VisitorError> {
        let Some(ref active_expr) = self.active_expr else {
            return Ok(());
        };
        let bad_handle = move || VisitorError::bad_handle(*active_expr);
        self.subexpr_map
            .get(active_expr)
            .ok_or_else(bad_handle)?
            .try_borrow_mut()
            .map_or_else(
                |_| Err(bad_handle()),
                |mut s| {
                    s.insert(base);
                    Ok(())
                },
            )
    }

    /// Union the read set for the active expression with the read set of the other expression.
    fn union_reads_with_active(&self, other: Handle<Expression>) -> Result<(), VisitorError> {
        let Some(ref active_expr) = self.active_expr else {
            return Ok(());
        };
        let bad_active = move || VisitorError::bad_handle(*active_expr);
        let bad_passed = move || VisitorError::bad_handle(other);
        let other_set = self
            .subexpr_map
            .get(&other)
            .ok_or_else(bad_passed)?
            .try_borrow()
            .map_err(|_| bad_passed())?;
        self.subexpr_map
            .get(active_expr)
            .ok_or_else(bad_active)?
            .try_borrow_mut()
            .map_or_else(
                |_| Err(bad_active()),
                |mut s| {
                    s.extend(other_set.iter());
                    Ok(())
                },
            )
    }
}

impl ExpressionVisitor<VisitorError> for VarVisitor<'_> {
    /// Determine whether the expression has been visited or not.
    ///
    /// If `handle` has already been visited (i.e. its read set has already been initialized), then
    /// the read set of the active expression is unioned with `handle`'s read set, and `false` is returned.
    ///
    /// Otherwise, `handle`'s read set is initialized to an empty set, the active expression is pushed onto the stack,
    /// and `true` is returned.
    ///
    /// # Errors
    /// [`VisitorError::BadHandle`] if the expression handle is not in the handle map,
    /// if the active handle's corresponding entry is borrowed mutably,
    /// or if the handle exists and its corresponding entry is borrowed mutably.
    ///
    /// [`VisitorError::BadHandle`]: crate::VisitorError::BadHandle
    #[allow(clippy::map_entry)] // We can't use a get or insert with here.
    fn before_visit(
        &mut self,
        handle: Handle<Expression>,
        _arena: &Arena<Expression>,
    ) -> Result<bool, VisitorError> {
        if self.subexpr_map.contains_key(&handle) {
            if self.active_expr.is_some() {
                self.union_reads_with_active(handle)?;
            }
            Ok(false)
        } else {
            self.subexpr_map.insert(handle, Default::default());
            if let Some(active) = self.active_expr {
                self.expr_stack.push(active);
            }
            self.active_expr = Some(handle);
            Ok(true)
        }
    }

    /// Finalize the visit of the expression.
    ///
    /// Marks the expression as visited by inserting the active set into the handle map.
    /// Then, restores the old active set.
    fn after_visit(
        &mut self,
        handle: Handle<Expression>,
        result: Result<(), VisitorError>,
    ) -> Result<(), VisitorError> {
        self.active_expr = self.expr_stack.pop();
        self.union_reads_with_active(handle)?;
        result
    }

    /// Adds this local variable to the active set.
    ///
    /// Also visits the initializer, if it exists.
    ///
    /// # Errors
    /// If an initializer for the local variable exists, propagates errors from visiting it.
    /// Propagates errors from calling to [`add_to_active`] on `local`
    ///
    /// [`add_to_active`]: VarVisitor::add_to_active
    fn visit_local_variable(
        &mut self,
        local: Handle<LocalVariable>,
        arena: &Arena<Expression>,
    ) -> Result<(), VisitorError> {
        // If the local variable has an initializer, we visit it.
        if let Some(init) = self.lvar_arena[local].init {
            self.visit(init, arena)?;
        }
        self.add_to_active(TrackedVar::LocalVariable(local))
    }

    /// Adds the global variable to the active set.
    ///
    /// Does NOT visit the initializer.  This
    /// must be done later on.
    fn visit_GlobalVariable(&mut self, global: Handle<GlobalVariable>) -> Result<(), VisitorError> {
        self.add_to_active(TrackedVar::GlobalVariable(global))
    }

    /// Adds the function argument to the active set.
    ///
    /// # Errors
    /// [`VisitorError::EmptyExpressionStack`] if there is no active expression.
    fn visit_FunctionArgument(&mut self, index: u32) -> Result<(), VisitorError> {
        self.add_to_active(TrackedVar::FunctionArgument(index))
    }

    /// Visit the base and index, then, calls `self.is_indexable` to check if the `base`
    /// is indexable, and if it is, marks every expression in the expression stack
    /// as containing an index access, and adds every expression in the read set of `index`
    /// as a dependency for an index access.
    fn visit_Access(
        &mut self,
        base: Handle<Expression>,
        index: Handle<Expression>,
        arena: &Arena<Expression>,
    ) -> Result<(), VisitorError> {
        self.visit(base, arena)?;

        self.visit(index, arena)?;

        if (self.is_indexable)(base) {
            self.exprs_with_accesses.extend(self.expr_stack.iter());
            self.exprs_with_accesses.insert(
                self.active_expr
                    .expect("There should always be an active expression in visitor methods"),
            );
            self.index_access_dependencies.extend(
                self.subexpr_map
                    .get(&index)
                    .ok_or_else(|| VisitorError::bad_handle(index))?
                    .try_borrow()
                    .map_err(|_| VisitorError::bad_handle(index))?
                    .iter(),
            );
        }
        Ok(())
    }

    /// Visit the base and index.
    /// Then, calls `self.is_indexable` to check if the `base` is indexable, and, if it is,
    /// marks all expressions in the expression stack as containing an index access.
    fn visit_AccessIndex(
        &mut self,
        base: Handle<Expression>,
        index: u32,
        arena: &Arena<Expression>,
    ) -> Result<(), VisitorError> {
        self.visit(base, arena)?;

        if (self.is_indexable)(base) {
            self.exprs_with_accesses.extend(self.expr_stack.iter());
            self.exprs_with_accesses.insert(
                self.active_expr
                    .expect("There should always be an active expression in visitor methods"),
            );
        }
        Ok(())
    }
}
// If we saw a break, then we stop iterating future items in the block.

#[cfg(all(test, feature = "wgsl-in"))]
mod tests {
    use super::*;
    use crate::front::wgsl::parse_str;
    use crate::span::SpanProvider;
    use crate::valid::{Capabilities, ValidationFlags, Validator};

    impl Handle<Expression> {
        fn print_expr<'a>(self, arena: &Arena<Expression>, input: &'a str) -> &'a str {
            // print the expression from the arena
            // get the item in the arena.
            let expr = arena.get_span(self);

            input.get(expr.to_range().unwrap()).unwrap()
        }
    }
    macro_rules! test_harness {
        ($wgsl:expr, $module:ident,$validated:ident) => {
            let $module = parse_str($wgsl).unwrap();
            let mut validator = Validator::new(ValidationFlags::all(), Capabilities::all());
            let $validated = validator.validate(&$module).unwrap();
        };
    }
    // Test that expressions are properly added.
    #[test]
    fn test_simple() {
        test_harness!(
            r#"
            fn main() {
                let b = vec2u(1u, 1u);
                let a = b[0];
            }
            "#,
            module,
            validated
        );
        // get function 0
        let (fun_handle, fun) = module.functions.iter().next().unwrap();

        let mut result = VarVisitor::visit_arena(
            &fun.expressions,
            &fun.local_variables,
            &module.global_variables,
            &module.global_expressions,
            Box::new(|_| true),
        )
        .expect("Visitor should not fail.");

        // We need to get the handle for the expression named `a`.
        let a_expr_handle = fun
            .expressions
            .iter()
            .find(|&(ref expr_handle, _)| {
                fun.named_expressions
                    .get(expr_handle)
                    .is_some_and(|name| name == "a")
            })
            .expect("Expression `a` should exist in the function.")
            .0;
        assert!(result.exprs_with_accesses.contains(&a_expr_handle));
        // We need to check that we have
    }

    #[test]
    fn test_complex() {
        let input = r#"@group(0) @binding(0) var<storage, read_write> a: array<u32>;
            @group(0) @binding(1) var<storage> control: u32;
            @group(0) @binding(1) var<storage, read_write> idx: u32;
            fn foo(i: u32) {
                if (control < 10u) {
                    a[idx] = control;
                }
            }"#;
        test_harness!(input, module, validated);

        let (fun_handle, fun) = module.functions.iter().next().unwrap();

        let mut result = VarVisitor::visit_arena(
            &fun.expressions,
            &fun.local_variables,
            &module.global_variables,
            &module.global_expressions,
            Box::new(|_| true),
        )
        .expect("Visitor should not fail.");

        result.exprs_with_accesses.iter().for_each(|f| {
            println!("{}", f.print_expr(&fun.expressions, input));
        });

    }
}
