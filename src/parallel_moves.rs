//! Parallel move solving.

use crate::EntityRepr;
use core::marker::PhantomData;

// TODO: stack-to-stack moves: choose the current coldest register, spill it to
// an emergency stack slot, load src to reg, store reg to dst, load original reg
// value from emergency stack slot. I think we should only ever need one
// emergency spill slot?

#[expect(dead_code, reason = "will probably need it")]
pub struct ParallelMoveSolver<E>
where
    E: EntityRepr,
{
    _todo: PhantomData<E>,
}

#[cfg(test)]
mod tests {
    // TODO: mutatis-based property test. take arbitrary set of moves (each dst
    // written exactly once), run them through the solver, interpret the result
    // and make sure it matches expectation.
}
