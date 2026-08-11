use crate::entity::EntityRepr;
use crate::error::IResult;
use crate::input::InputFunction;
use crate::output::OutputInner;

pub(crate) fn validate<E>(func: &impl InputFunction, output: &mut OutputInner<E>) -> IResult<()>
where
    E: EntityRepr,
{
    let _ = (func, output);
    todo!("validate the input function's SSA, basic blocks, etc...")
}
