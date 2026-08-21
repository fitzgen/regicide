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

    // TODO: fixed-point data-flow analysis to find (a) moves that simply move
    // the value that is already in that location into that location again, and
    // (b) moves that can be replaced with rematerialization.

    todo!()
}
