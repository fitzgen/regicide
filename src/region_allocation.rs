use crate::context::ContextInner;
use crate::entity::EntityRepr;
use crate::error::IResult;
use crate::function::Function;

pub(crate) fn region_allocation<E>(
    context: &mut ContextInner<E>,
    func: &impl Function,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _ = (context, func);
    todo!()
}
