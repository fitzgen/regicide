//! Coalesces and pre-colors bundles based on fixed-register constraints in a
//! bottom-up pass over the region tree.

use crate::context::ContextInner;
use crate::entity::EntityRepr;
use crate::error::IResult;
use crate::function::InputFunction;
use crate::timing::Timing;

pub(crate) fn partial_allocate<E>(
    context: &mut ContextInner<E>,
    func: &impl InputFunction,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("partial allocate");
    let _ = (context, func);
    todo!()
}
