/*!
Definition of the `StatementVisitor` trait.
*/

use crate::{Block, Expression, Function, Handle, Range, Statement, SwitchCase};

/// The `StatementVisitor` trait is used to visit the statements in a shader module.
///
/// The entry point to the visitor is the `default_visit_Statement` method. All this does is
/// match on the kind of `Statement` passed, dispatching to the its corresponding `visit_` method.
///
/// The `visit_` methods are the ones that should be implemented by the trait implementations.  This is
/// where the logic for visiting the statements should be implemented.
#[allow(non_snake_case, unused_variables)]
pub trait StatementVisitor<T> {
    /// Match on the type of the Statement enum and calls the matching visit method.
    /// This is provided as a default implementation for the trait. It should not be overridden.
    ///
    /// Trait implementations should not override this method. Instead, they should override `visit_Statement`.
    fn default_visit_Statement(&mut self, statement: &Statement) -> Result<(), T> {
        use Statement as S;
        match *statement {
            S::Emit(ref expressions) => self.visit_Emit(expressions)?,
            S::Block(ref block) => self.visit_Block(block)?,
            S::If {
                condition,
                ref accept,
                ref reject,
            } => self.visit_If(condition, accept, reject)?,
            S::Switch {
                selector,
                ref cases,
            } => self.visit_Switch(selector, cases)?,
            S::Loop {
                ref body,
                ref continuing,
                break_if,
            } => self.visit_Loop(body, continuing, break_if)?,
            S::Break => self.visit_Break()?,
            S::Continue => self.visit_Continue()?,
            S::Return { value } => self.visit_Return(value)?,
            S::Kill => self.visit_Kill()?,
            S::Barrier(Barrier) => self.visit_Barrier(Barrier)?,
            S::Store { pointer, value } => self.visit_Store(pointer, value)?,
            S::ImageStore {
                image,
                coordinate,
                array_index,
                value,
            } => self.visit_ImageStore(image, coordinate, array_index, value)?,
            S::Atomic {
                pointer,
                fun,
                value,
                result,
            } => self.visit_Atomic(pointer, fun, value, result)?,
            S::WorkGroupUniformLoad { pointer, result } => {
                self.visit_WorkGroupUniformLoad(pointer, result)?;
            }
            S::Call {
                function,
                ref arguments,
                result,
            } => self.visit_Call(function, arguments, result)?,
            S::RayQuery { query, ref fun } => self.visit_RayQuery(query, fun)?,
            S::SubgroupBallot { result, predicate } => {
                self.visit_SubgroupBallot(result, predicate)?;
            }
            S::SubgroupGather {
                mode,
                argument,
                result,
            } => self.visit_SubgroupGather(mode, argument, result)?,
            S::SubgroupCollectiveOperation {
                op,
                collective_op,
                argument,
                result,
            } => self.visit_SubgroupCollectiveOperation(op, collective_op, argument, result)?,
        };
        Ok(())
    }

    fn default_visit_Block(&mut self, block: &Block) -> Result<(), T> {
        for statement in block {
            self.visit_Statement(statement)?;
        }
        Ok(())
    }
    fn visit_Statement(&mut self, statement: &Statement) -> Result<(), T> {
        self.default_visit_Statement(statement)?;
        Ok(())
    }
    fn visit_Emit(&mut self, r: &Range<Expression>) -> Result<(), T> {
        Ok(())
    }

    fn visit_Block(&mut self, block: &Block) -> Result<(), T> {
        self.default_visit_Block(block)?;
        Ok(())
    }

    fn visit_If(
        &mut self,
        condition: Handle<Expression>,
        accept: &Block,
        reject: &Block,
    ) -> Result<(), T> {
        self.visit_Block(accept)?;
        self.visit_Block(reject)?;
        Ok(())
    }

    fn visit_Switch(
        &mut self,
        selector: Handle<Expression>,
        cases: &Vec<SwitchCase>,
    ) -> Result<(), T> {
        for case in cases {
            self.visit_Block(&case.body)?;
        }
        Ok(())
    }

    fn visit_Loop(
        &mut self,
        body: &Block,
        continuing: &Block,
        break_if: Option<Handle<Expression>>,
    ) -> Result<(), T> {
        self.visit_Block(body)?;
        self.visit_Block(continuing)?;
        Ok(())
    }

    fn visit_Break(&mut self) -> Result<(), T> {
        Ok(())
    }

    fn visit_Continue(&mut self) -> Result<(), T> {
        Ok(())
    }

    fn visit_Return(&mut self, value: Option<Handle<Expression>>) -> Result<(), T> {
        Ok(())
    }

    fn visit_Kill(&mut self) -> Result<(), T> {
        Ok(())
    }

    fn visit_Barrier(&mut self, barrier: crate::Barrier) -> Result<(), T> {
        Ok(())
    }

    fn visit_Store(
        &mut self,
        pointer: Handle<Expression>,
        value: Handle<Expression>,
    ) -> Result<(), T> {
        Ok(())
    }

    fn visit_ImageStore(
        &mut self,
        image: Handle<Expression>,
        coordinate: Handle<Expression>,
        array_index: Option<Handle<Expression>>,
        value: Handle<Expression>,
    ) -> Result<(), T> {
        Ok(())
    }

    fn visit_Atomic(
        &mut self,
        pointer: Handle<Expression>,
        fun: crate::AtomicFunction,
        value: Handle<Expression>,
        result: Option<Handle<Expression>>,
    ) -> Result<(), T> {
        Ok(())
    }

    fn visit_WorkGroupUniformLoad(
        &mut self,
        pointer: Handle<Expression>,
        result: Handle<Expression>,
    ) -> Result<(), T> {
        Ok(())
    }

    fn visit_Call(
        &mut self,
        function: Handle<Function>,
        arguments: &[Handle<Expression>],
        result: Option<Handle<Expression>>,
    ) -> Result<(), T> {
        Ok(())
    }

    fn visit_RayQuery(
        &mut self,
        query: Handle<Expression>,
        fun: &crate::RayQueryFunction,
    ) -> Result<(), T> {
        Ok(())
    }

    fn visit_SubgroupBallot(
        &mut self,
        result: Handle<Expression>,
        predicate: Option<Handle<Expression>>,
    ) -> Result<(), T> {
        Ok(())
    }

    fn visit_SubgroupGather(
        &mut self,
        mode: crate::GatherMode,
        argument: Handle<Expression>,
        result: Handle<Expression>,
    ) -> Result<(), T> {
        Ok(())
    }

    fn visit_SubgroupCollectiveOperation(
        &mut self,
        op: crate::SubgroupOperation,
        collective_op: crate::CollectiveOperation,
        argument: Handle<Expression>,
        result: Handle<Expression>,
    ) -> Result<(), T> {
        Ok(())
    }
}
