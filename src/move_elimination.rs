//! Move elimination.
//!
//! TODO: overview

use crate::Input;
use crate::context::ContextInner;
use crate::entity::EntityRepr;
use crate::error::IResult;
use crate::input::{InputFunction, MoveEliminationLevel};
use crate::timing::Timing;

pub(crate) fn eliminate_moves<E>(
    context: &mut ContextInner<E>,
    input: &Input<'_, impl InputFunction>,
) -> IResult<()>
where
    E: EntityRepr,
{
    if input.options.move_elimination_level == MoveEliminationLevel::None
        // TODO: actually implement move elimination
        || true
    {
        return Ok(());
    }

    let _timing = Timing::new("eliminate moves");

    let _ = context;

    // TODO: use the results of that analysis to eliminate redundant moves:
    // moves that put a value V into location L when L already contains V.

    todo!()
}
