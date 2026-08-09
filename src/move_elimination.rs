use crate::context::ContextInner;
use crate::entity::EntityRepr;
use crate::error::IResult;
use crate::function::InputFunction;
use crate::timing::Timing;

pub(crate) fn eliminate_moves<E>(context: &mut ContextInner<E>, func: &impl InputFunction) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("eliminate moves");
    let _ = (context, func);
    todo!()
}
