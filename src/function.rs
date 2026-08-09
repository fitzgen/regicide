use crate::entity::Val;

/// TODO FITZGEN
pub trait Function {
    /// TODO FITZGEN
    fn len_values(&self) -> usize;

    /// TODO FITZGEN
    fn remat_cost(&self, val: Val) -> Option<RematCost>;

    // TODO: ...
}

/// The cost of rematerializing a value, rather than shuffling it between
/// registers or reloading it from a spill slot.
pub enum RematCost {
    /// Always rematerialize this value on demand.
    ///
    /// Eagerly split its live range bundle to minimal ranges. It should never
    /// be shuffled between registers or spilled.
    AlwaysRemat = 0,

    /// When its operands are already available, rematerializing this value is
    /// cheaper than keeping it alive in a register and moving it around.
    CheaperThanMove = 1,

    /// When its operands are already available, rematerializing this value is
    /// cheaper than reloading it from a spill slot, but not cheaper than
    /// shuffling it between registers.
    CheaperThanReload = 2,
}
