//! Spill slots.

use crate::context::ContextInner;
use crate::entity::EntityRepr;
use crate::error::IResult;
use crate::input::InputFunction;
use crate::timing::Timing;

pub(crate) fn allocate_spill_slots<E>(
    context: &mut ContextInner<E>,
    func: &impl InputFunction,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _timing = Timing::new("allocate spill slots");
    let _ = (context, func);
    todo!(
        "do classic O(n^2) SSA chordal regalloc, with not splitting or \
         coalescing; can do a single pass dataflow analysis to figure out max \
         live stack slots per size class"
    )
}
