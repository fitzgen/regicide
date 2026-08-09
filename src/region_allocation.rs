use crate::context::ContextInner;
use crate::entity::EntityRepr;
use crate::error::IResult;
use crate::function::Function;
use crate::timing::Timing;

pub(crate) fn region_allocate<E>(context: &mut ContextInner<E>, func: &impl Function) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("region allocate");
    let _ = (context, func);
    todo!()
}
