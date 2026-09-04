//! Move elimination.
//!
//! TODO: overview

use crate::context::ContextInner;
use crate::entity::EntityRepr;
use crate::error::IResult;
use crate::input::InputFunction;
use crate::timing::Timing;

pub(crate) fn eliminate_moves<E>(
    context: &mut ContextInner<E>,
    func: &impl InputFunction,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("eliminate moves");
    let _ = (context, func);

    // TODO: add `InputOptions` field for whether to do a full, global fixpoint
    // (regalloc3 style) or block-local, single-pass (regalloc2 style) dataflow
    // analysis / abstract interpretation to determine what registers and spill
    // slots hold which value at each program point. Default to the full
    // fixpoint.
    //
    // TODO: use the results of that analysis to eliminate redundant moves:
    // moves that put a value V into location L when L already contains V.

    todo!()
}
