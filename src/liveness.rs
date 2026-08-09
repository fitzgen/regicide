use crate::{
    btree::{BTreeSet, BTreeSetArena},
    entity::{Block, EntityRepr, SecondaryMap, Val},
    error::IResult,
    function::Function,
    timing::Timing,
};
use alloc::vec::Vec;

pub struct Liveness<E>
where
    E: EntityRepr,
{
    arena: BTreeSetArena<E, Val<E>>,
    live_in: SecondaryMap<Block<E>, BTreeSet<E, Val<E>>>,
    live_out: SecondaryMap<Block<E>, BTreeSet<E, Val<E>>>,
    worklist: Vec<Block<E>>,
}

impl<E> Liveness<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        Liveness {
            arena: BTreeSetArena::new(),
            live_in: SecondaryMap::new(BTreeSet::new()),
            live_out: SecondaryMap::new(BTreeSet::new()),
            worklist: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            arena,
            live_in,
            live_out,
            worklist,
        } = self;
        arena.reset();
        live_in.reset();
        live_out.reset();
        worklist.clear();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            arena,
            live_in,
            live_out,
            worklist,
        } = self;
        arena.is_reset() && live_in.is_reset() && live_out.is_reset() && worklist.is_empty()
    }

    pub fn construct(&mut self, func: &impl Function) -> IResult<()> {
        let _timing = Timing::new("liveness");
        // TODO
        let _ = func;
        Ok(())
    }
}
