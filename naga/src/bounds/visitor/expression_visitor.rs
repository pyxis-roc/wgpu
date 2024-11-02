use crate::{Arena, Expression, Function, GlobalVariable, Handle, LocalVariable, Statement};

/// Expands to
/// ```rust,exclude
/// $handle.map_or(
///     Ok(()),
///     |handle|
///         if self.should_visit(handle, arena) {
///             self.default_visit(handle, arena)
///         } else {
///             Ok(())
///         }
///   )
/// ```
macro_rules! visit_if(
    (@option $self:ident, $handle:expr, $arena:ident) => {
        $handle.map_or(Ok(()), |handle| $self.visit(handle, $arena))
    }
);

/// This is a visitor that visits expressions.
///
/// Comes with default implementations that visits all sub expressions in the expression.
/// Before visiting a sub-expression, [`should_visit`] is called to determine whether or not the sub-expression should be visited.
///
/// The default implementation of `should_visit` always returns true, but this is meant to be overridden to allow for things like not visiting expressions
/// that have already been visited.
/// The default visitor method for each expression just calls visit on all sub expressions. It does nothing with the expression itself or with any fields
/// that the expression may have.
/// The default visit methods for expressions that do not have sub expressions do nothing.
///
/// [`should_visit`]: ExpressionVisitor::should_visit
#[allow(unused_variables, non_snake_case)] // our visitor methods mirror the name of the expression variant.
pub trait ExpressionVisitor<T> {
    /// Method that is called prior to visiting an expression.
    ///
    /// This method returns a boolean indicating whether or not the expression should be visited.
    #[inline(always)]
    fn before_visit(
        &mut self,
        handle: Handle<Expression>,
        arena: &Arena<Expression>,
    ) -> Result<bool, T> {
        Ok(true)
    }

    /// Invoked after visiting an expression. Does nothing by default.
    ///
    /// This method is called after visiting an expression, and is passed the handle of the expression that was visited.
    ///
    /// Useful for any cleanup that needs to be done after visiting an expression.
    #[inline(always)]
    fn after_visit(&mut self, handle: Handle<Expression>, result: Result<(), T>) -> Result<(), T> {
        result
    }
    /// Default visitor method for expression.
    ///
    /// This method just contains a match statement that matches on the expression variant and calls the appropriate visit method.
    fn visit(&mut self, handle: Handle<Expression>, arena: &Arena<Expression>) -> Result<(), T> {
        if !self.before_visit(handle, arena)? {
            return Ok(());
        };
        use Expression as E;
        let res = match arena[handle] {
            E::Literal(l) => self.visit_Literal(l),
            E::Constant(c) => self.visit_constant(c),
            E::Override(o) => self.visit_Override(o),
            E::ZeroValue(t) => self.visit_ZeroValue(t),
            E::Compose { ty, ref components } => self.visit_Compose(ty, components, arena),
            E::Access { base, index } => self.visit_Access(base, index, arena),
            E::AccessIndex { base, index } => self.visit_AccessIndex(base, index, arena),
            E::Splat { size, value } => self.visit_Splat(size, value, arena),
            E::Swizzle {
                size,
                vector,
                ref pattern,
            } => self.visit_Swizzle(size, vector, pattern, arena),
            E::FunctionArgument(index) => self.visit_FunctionArgument(index),
            E::GlobalVariable(g) => self.visit_GlobalVariable(g),
            E::LocalVariable(l) => self.visit_local_variable(l, arena),
            E::Load { pointer } => self.visit_Load(pointer, arena),
            E::ImageSample {
                image,
                sampler,
                gather,
                coordinate,
                array_index,
                offset,
                level,
                depth_ref,
            } => self.visit_ImageSample(
                image,
                sampler,
                gather,
                coordinate,
                array_index,
                offset,
                level,
                depth_ref,
                arena,
            ),
            E::ImageLoad {
                image,
                coordinate,
                array_index,
                sample,
                level,
            } => self.visit_ImageLoad(image, coordinate, array_index, sample, level, arena),
            E::ImageQuery { image, query } => self.visit_ImageQuery(image, query, arena),
            E::Unary { op, expr } => self.visit_Unary(expr, op, arena),
            E::Binary { op, left, right } => self.visit_Binary(left, right, op, arena),
            E::Select {
                condition,
                accept,
                reject,
            } => self.visit_Select(condition, accept, reject, arena),
            E::Derivative { axis, ctrl, expr } => self.visit_Derivative(axis, expr, arena),
            E::Relational { fun, argument } => self.visit_Relational(fun, argument, arena),
            E::Math {
                fun,
                arg,
                arg1,
                arg2,
                arg3,
            } => self.visit_Math(fun, arg, arg1, arg2, arg3, arena),
            E::As {
                expr,
                kind,
                convert,
            } => self.visit_As(expr, kind, convert, arena),
            E::ArrayLength(expr) => self.visit_ArrayLength(expr, arena),
            E::CallResult(f) => self.visit_CallResult(f),
            E::AtomicResult { ty, comparison } => self.visit_AtomicResult(ty, comparison),
            E::WorkGroupUniformLoadResult { ty } => self.visit_WorkGroupUniformLoadResult(ty),
            E::RayQueryProceedResult => self.visit_RayQueryProceedResult(),
            E::RayQueryGetIntersection { query, committed } => {
                self.visit_RayQueryGetIntersection(query, committed, arena)
            }
            E::SubgroupBallotResult => self.visit_SubgroupBallotResult(),
            E::SubgroupOperationResult { ty } => self.visit_SubgroupOperationResult(ty),
        };
        self.after_visit(handle, res)
    }

    /// Visitor method for [`Literal`] expressions. The default trait implementation does nothing.
    ///
    /// [`Literal`]: crate::Expression::Literal
    fn visit_Literal(&mut self, literal: crate::Literal) -> Result<(), T> {
        Ok(())
    }

    /// Visitor method for [`Constant`] expressions. The default trait implementation does nothing.
    ///
    /// [`Constant`]: crate::Expression::Constant
    fn visit_constant(&mut self, constant: Handle<crate::Constant>) -> Result<(), T> {
        Ok(())
    }

    /// Visitor method for [`Override`] expressions. The default trait implementation does nothing.
    ///
    /// [`Override`]: crate::Expression::Override
    fn visit_Override(&mut self, o: Handle<crate::Override>) -> Result<(), T> {
        Ok(())
    }

    /// Visitor method for [`ZeroValue`] expressions. The default trait implementation does nothing.
    ///
    /// [`ZeroValue`]: crate::Expression::ZeroValue
    fn visit_ZeroValue(&mut self, ty: Handle<crate::Type>) -> Result<(), T> {
        Ok(())
    }

    /// Visitor method for [`Compose`] expressions. The default trait implementation visits all components.
    ///
    /// [`Compose`]: crate::Expression::Compose
    /// [`components`]: crate::Expression::Compose::components
    fn visit_Compose(
        &mut self,
        ty: Handle<crate::Type>,
        exprs: &[Handle<Expression>],
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        for expr in exprs {
            self.visit(*expr, arena)?;
        }
        Ok(())
    }

    /// Visitor method for [`Access`] expressions.
    ///
    /// [`Access`]: crate::Expression::Access
    fn visit_Access(
        &mut self,
        base: Handle<Expression>,
        index: Handle<Expression>,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(base, arena)?;
        self.visit(index, arena)
    }

    /// Visitor method for [`AccessIndex`] expressions.
    ///
    /// [`AccessIndex`]: crate::Expression::AccessIndex
    fn visit_AccessIndex(
        &mut self,
        base: Handle<Expression>,
        index: u32,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(base, arena)
    }

    /// Visitor method for [`Splat`] expressions.
    ///
    /// [`Splat`]: crate::Expression::Splat
    fn visit_Splat(
        &mut self,
        size: crate::VectorSize,
        value: Handle<Expression>,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(value, arena)
    }

    /// Visitor method for [`Swizzle`] expressions.
    ///
    /// [`Swizzle`]: crate::Expression::Swizzle
    fn visit_Swizzle(
        &mut self,
        size: crate::VectorSize,
        vector: Handle<Expression>,
        pattern: &[crate::SwizzleComponent; 4],
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(vector, arena)
    }

    /// Visitor method for [`FunctionArgument`] expressions.
    ///
    /// There are no sub-expressions to visit, so the default implementation does nothing.
    ///
    /// [`FunctionArgument`]: crate::Expression::FunctionArgument
    fn visit_FunctionArgument(&mut self, index: u32) -> Result<(), T> {
        Ok(())
    }

    /// Visitor method for [`GlobalVariable`] expressions.
    ///
    /// There are no sub-expressions to visit, so the default implementation does nothing.
    ///
    /// [`GlobalVariable`]: crate::Expression::GlobalVariable
    fn visit_GlobalVariable(&mut self, global: Handle<GlobalVariable>) -> Result<(), T> {
        Ok(())
    }

    /// Visitor method for [`LocalVariable`] expressions.
    ///
    /// There are no sub-expressions to visit, so the default implementation does nothing.
    ///
    /// [`LocalVariable`]: crate::Expression::LocalVariable
    fn visit_local_variable(
        &mut self,
        local: Handle<LocalVariable>,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        Ok(())
    }

    /// Visitor method for [`Load`] expressions.
    ///
    /// [`Load`]: crate::Expression::Load
    fn visit_Load(
        &mut self,
        pointer: Handle<Expression>,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(pointer, arena)
    }

    /// Visitor method for [`ImageSample`] expressions.
    ///
    /// # Notes
    /// `ImageSample` contains an `offset` sub-expression, although this is not visited by the default implementation
    /// as it refers to an expression in [`Module::global_expressions`], and the arena we have might be different.
    ///
    /// [`ImageSample`]: crate::Expression::ImageSample
    ///
    /// [`Module::global_expressions`]: crate::Module::global_expressions
    #[allow(clippy::too_many_arguments)] // This is just how many arguments there are to image sample. We are not destructuring.
    fn visit_ImageSample(
        &mut self,
        image: Handle<Expression>,
        sampler: Handle<Expression>,
        gather: Option<crate::SwizzleComponent>,
        coordinate: Handle<Expression>,
        array_index: Option<Handle<Expression>>,
        offset: Option<Handle<Expression>>,
        level: crate::SampleLevel,
        depth_ref: Option<Handle<Expression>>,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(image, arena)?;
        self.visit(sampler, arena)?;
        self.visit(coordinate, arena)?;
        visit_if!(@option self, array_index, arena)?;
        visit_if!(@option self, depth_ref, arena)?;
        Ok(())
    }

    /// Visitor method for [`ImageLoad`] expressions.
    ///
    /// [`ImageLoad`]: crate::Expression::ImageLoad
    fn visit_ImageLoad(
        &mut self,
        image: Handle<Expression>,
        coordinate: Handle<Expression>,
        array_index: Option<Handle<Expression>>,
        sample: Option<Handle<Expression>>,
        level: Option<Handle<Expression>>,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(image, arena)?;
        self.visit(coordinate, arena)?;
        visit_if!(@option self, array_index, arena)?;
        visit_if!(@option self, sample, arena)?;
        visit_if!(@option self, level, arena)
    }

    /// Visitor method for [`ImageQuery`] expressions.
    ///
    /// [`ImageQuery`]: crate::Expression::ImageQuery
    fn visit_ImageQuery(
        &mut self,
        image: Handle<Expression>,
        query: crate::ImageQuery,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(image, arena)
    }

    /// Visitor method for [`Unary`] expressions.
    ///
    /// [`Unary`]: crate::Expression::Unary
    fn visit_Unary(
        &mut self,
        expr: Handle<Expression>,
        op: crate::UnaryOperator,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(expr, arena)
    }

    /// Visitor method for [`Binary`] expressions.
    ///
    /// [`Binary`]: crate::Expression::Binary
    fn visit_Binary(
        &mut self,
        left: Handle<Expression>,
        right: Handle<Expression>,
        op: crate::BinaryOperator,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(left, arena)?;
        self.visit(right, arena)
    }

    /// Visitor method for [`Select`] expressions.
    ///
    /// [`Select`]: crate::Expression::Select
    fn visit_Select(
        &mut self,
        condition: Handle<Expression>,
        accept: Handle<Expression>,
        reject: Handle<Expression>,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(condition, arena)?;
        self.visit(accept, arena)?;
        self.visit(reject, arena)
    }

    /// Visitor method for [`Derivative`] expressions.
    ///
    /// [`Derivative`]: crate::Expression::Derivative
    fn visit_Derivative(
        &mut self,
        axis: crate::DerivativeAxis,
        expr: Handle<Expression>,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(expr, arena)
    }

    /// Visitor method for [`Relational`] expressions.
    ///
    /// [`Relational`]: crate::Expression::Relational
    fn visit_Relational(
        &mut self,
        fun: crate::RelationalFunction,
        argument: Handle<Expression>,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(argument, arena)
    }

    /// Visitor method for [`Math`] expressions.
    ///
    /// [`Math`]: crate::Expression::Math
    fn visit_Math(
        &mut self,
        fun: crate::MathFunction,
        arg: Handle<Expression>,
        arg1: Option<Handle<Expression>>,
        arg2: Option<Handle<Expression>>,
        arg3: Option<Handle<Expression>>,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(arg, arena)?;
        visit_if!(@option self, arg1, arena)?;
        visit_if!(@option self, arg2, arena)?;
        visit_if!(@option self, arg3, arena)
    }

    /// Visitor method for [`As`] expressions.
    ///
    /// [`As`]: crate::Expression::As
    fn visit_As(
        &mut self,
        expr: Handle<Expression>,
        kind: crate::ScalarKind,
        convert: Option<u8>,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(expr, arena)
    }

    /// Visitor method for [`CallResult`] expressions.
    ///
    /// Has no sub-expressions, so does nothing.
    ///
    /// [`Call`]: crate::Expression::CallResult
    fn visit_CallResult(&mut self, function: Handle<Function>) -> Result<(), T> {
        Ok(())
    }

    /// Visitor method for [`AtomicResult`] expressions.
    ///
    /// Has no sub-expressions, so the default implementation does nothing.
    ///
    /// [`AtomicResult`]: crate::Expression::AtomicResult
    fn visit_AtomicResult(&mut self, ty: Handle<crate::Type>, comparison: bool) -> Result<(), T> {
        Ok(())
    }

    /// Visitor method for [`WorkGroupUniformLoadResult`] expressions.
    ///
    /// Has no sub-expressions, so the default implementation does nothing.
    ///
    /// [`WorkGroupUniformLoadResult`]: crate::Expression::WorkGroupUniformLoadResult
    fn visit_WorkGroupUniformLoadResult(&mut self, ty: Handle<crate::Type>) -> Result<(), T> {
        Ok(())
    }

    /// Visitor method for [`ArrayLength`] expressions.
    ///
    /// [`ArrayLength`]: crate::Expression::ArrayLength
    /// [`ArrayLength::expr`]: crate::Expression::ArrayLength::expr
    fn visit_ArrayLength(
        &mut self,
        expr: Handle<Expression>,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(expr, arena)
    }

    /// Visitor method for [`RayQueryProceedResult`] expressions.
    ///
    /// [`RayQueryProceedResult`]: crate::Expression::RayQueryProceedResult
    fn visit_RayQueryProceedResult(&mut self) -> Result<(), T> {
        Ok(())
    }

    /// Visitor method for [`RayQueryGetIntersection`] expressions.
    ///
    /// [`RayQueryGetIntersection`]: crate::Expression::RayQueryGetIntersection
    fn visit_RayQueryGetIntersection(
        &mut self,
        query: Handle<Expression>,
        committed: bool,
        arena: &Arena<Expression>,
    ) -> Result<(), T> {
        self.visit(query, arena)
    }

    /// Visitor method for [`SubgroupBallotResult`] expressions.
    ///
    /// Has no sub-expressions, so the default implementation does nothing.
    ///
    /// [`SubgroupBallotResult`]: crate::Expression::SubgroupBallotResult
    fn visit_SubgroupBallotResult(&mut self) -> Result<(), T> {
        Ok(())
    }

    /// Visitor method for [`SubgroupOperationResult`] expressions.
    ///
    /// Has no sub-expressions, so the default implementation does nothing.
    ///
    /// [`SubgroupOperationResult`]: crate::Expression::SubgroupOperationResult
    fn visit_SubgroupOperationResult(&mut self, ty: Handle<crate::Type>) -> Result<(), T> {
        Ok(())
    }
}
