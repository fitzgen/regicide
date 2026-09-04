//! Move generation.
//!
//! TODO: overview

use crate::context::ContextInner;
use crate::entity::EntityRepr;
use crate::error::IResult;
use crate::input::InputFunction;
use crate::timing::Timing;

pub(crate) fn generate_moves<E>(
    context: &mut ContextInner<E>,
    func: &impl InputFunction,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("generate moves");
    let _ = (context, func);

    // TODO: do regalloc2/3 style "half move" generation

    todo!()
}
