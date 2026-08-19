//! Coalesces and pre-colors bundles based on fixed-register constraints in a
//! bottom-up pass over the region tree.

use crate::context::ContextInner;
use crate::entity::EntityRepr;
use crate::error::IResult;
use crate::input::InputFunction;
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

    // TODO: bottom-up, post-order traversal of the region tree

    // TODO: visit blocks within each region in greatest to least estimated
    // frequency order. reuse the same temporary `Vec<Block<E>>` for sorting
    // each region's blocks.

    // TODO: coalescing: never coalesce bundles across regions. never coalesce
    // bundles with conflicting pre-coloring or register preferences. never
    // coalesce two bundles that conflict. cases to try coalescing: block
    // arguments with block params, two-address/tied/reused operands

    // TODO: for bundles that flow across regions, give them a register
    // preference based on the pre-color of the bundle they flow into, if any

    todo!()
}
