use crate::Entity;
use crate::context::ContextInner;
use crate::entity::{EntityRepr, Inst};
use crate::error::IResult;
use crate::function::Function;

pub enum ProgramPoint<E>
where
    E: EntityRepr,
{
    Before(Inst<E>),
    After(Inst<E>),
}

pub struct LiveRangeData<E>
where
    E: EntityRepr,
{
    pub start: ProgramPoint<E>,
    pub end: ProgramPoint<E>,
}

pub struct BundleData {
    // TODO
}

pub(crate) fn construct_live_ranges<E>(
    context: &mut ContextInner<E>,
    func: &impl Function,
) -> IResult<()>
where
    E: EntityRepr,
{
    let _ = (context, func);
    todo!()
}
