use crate::context::ContextInner;
use crate::entity::EntityRepr;
use crate::error::IResult;
use crate::input::InputFunction;
use crate::timing::Timing;

pub(crate) fn region_allocate<E>(
    context: &mut ContextInner<E>,
    func: &impl InputFunction,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("region allocate");

    // TODO: reset `LiveRanges::block_spans`, since this pass can split spans,
    // which invalidates that map.

    let _ = (context, func);
    todo!()
}
