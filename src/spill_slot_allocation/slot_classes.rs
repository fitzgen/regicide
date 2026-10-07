//! Slot classes: spilled block parameters and the arguments that feed them,
//! grouped so that the coloring walk can give each group one slot.
//!
//! A parameter in a different slot than its argument costs a stack-to-stack
//! move on that edge. So before the walk, we union parameters with their
//! arguments wherever their reservations do not overlap. One union can rule out
//! a later one, so we take the heaviest edges first. During the walk, the first
//! member of a class to be colored *promises* the class a slot: one whose other
//! promises its reservations do not overlap, so that later members find it
//! free.

use crate::{
    Block, Entity as _, Val,
    entity::{EntityRepr, EntitySet, SecondaryMap},
    error::{IResult, InternalError},
    input::{Input, InputBlock as _, InputFunction},
    interval_sets::{Fuel, IntervalSet, IntervalSetArena},
    live_ranges::LivePoint,
    output::OutputInner,
    region_tree::RegionTree,
    rpo::Rpo,
    spill_slot_allocation::SpillSlot,
    union_find::UnionFind,
};
use alloc::vec::Vec;

define_entities! {
    /// One stretch of a spilled value's slot reservation within a block.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct SlotRange = "slot_range";
}

/// The slot classes of one function's spilled values, and the slots promised
/// to them.
pub(super) struct SlotClasses<E>
where
    E: EntityRepr,
{
    /// Which values share a class.
    sets: UnionFind<Val<E>>,

    /// Each class root's reservations, until the class is promised a slot.
    class_ranges: SecondaryMap<Val<E>, Option<IntervalSet<SlotRange<E>>>>,

    /// The weight of the edges each class root joins: the moves breaking the
    /// class up would cost.
    class_weight: SecondaryMap<Val<E>, f64>,

    /// The slot each class root was promised.
    class_slot: SecondaryMap<Val<E>, Option<SpillSlot<E>>>,

    /// The reservations of every class promised each slot.
    slot_ranges: SecondaryMap<SpillSlot<E>, Option<IntervalSet<SlotRange<E>>>>,

    /// The total `class_weight` of the classes promised each slot.
    slot_weight: SecondaryMap<SpillSlot<E>, f64>,

    /// Storage for `class_ranges` and `slot_ranges`.
    range_arena: IntervalSetArena<SlotRange<E>, LivePoint<E>>,

    /// How many `SlotRange`s we have created.
    num_ranges: usize,

    /// The work left for overlap checks between ranges.
    fuel: u64,

    /// Where each value's reservation began in the block being recorded,
    /// while it is open.
    open_ranges: SecondaryMap<Val<E>, Option<LivePoint<E>>>,

    /// The values with an entry in `open_ranges`.
    open: Vec<Val<E>>,

    /// Spilled block-call arguments and the spilled parameters they feed, with
    /// the weight of the edge's move.
    affinities: Vec<(f64, Val<E>, Val<E>)>,

    /// The values in `affinities`, the only ones whose reservations we need.
    affine: EntitySet<Val<E>>,

    /// The total weight of each parameter's entries in `affinities`.
    param_weight: SecondaryMap<Val<E>, f64>,
}

impl<E> SlotClasses<E>
where
    E: EntityRepr,
{
    pub const fn new() -> Self {
        SlotClasses {
            sets: UnionFind::new(),
            class_ranges: SecondaryMap::new(None),
            class_weight: SecondaryMap::new(0.0),
            class_slot: SecondaryMap::new(None),
            slot_ranges: SecondaryMap::new(None),
            slot_weight: SecondaryMap::new(0.0),
            range_arena: IntervalSetArena::new(),
            num_ranges: 0,
            fuel: 0,
            open_ranges: SecondaryMap::new(None),
            open: Vec::new(),
            affinities: Vec::new(),
            affine: EntitySet::new(),
            param_weight: SecondaryMap::new(0.0),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            sets,
            class_ranges,
            class_weight,
            class_slot,
            slot_ranges,
            slot_weight,
            range_arena,
            num_ranges,
            fuel,
            open_ranges,
            open,
            affinities,
            affine,
            param_weight,
        } = self;
        sets.reset();
        class_ranges.reset();
        class_weight.reset();
        class_slot.reset();
        slot_ranges.reset();
        slot_weight.reset();
        range_arena.reset();
        *num_ranges = 0;
        *fuel = 0;
        open_ranges.reset();
        open.clear();
        affinities.clear();
        affine.reset();
        param_weight.reset();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            sets,
            class_ranges,
            class_weight,
            class_slot,
            slot_ranges,
            slot_weight,
            range_arena,
            num_ranges,
            fuel,
            open_ranges,
            open,
            affinities,
            affine,
            param_weight,
        } = self;
        sets.is_reset()
            && class_ranges.is_reset()
            && class_weight.is_reset()
            && class_slot.is_reset()
            && slot_ranges.is_reset()
            && slot_weight.is_reset()
            && range_arena.is_reset()
            && *num_ranges == 0
            && *fuel == 0
            && open_ranges.is_reset()
            && open.is_empty()
            && affinities.is_empty()
            && affine.is_reset()
            && param_weight.is_reset()
    }

    /// Record every spilled argument and the spilled parameter it feeds, both
    /// single slots of one size. Returns whether there were any.
    pub fn collect_affinities(
        &mut self,
        input: &Input<'_, impl InputFunction>,
        rpo: &Rpo<E>,
        region_tree: &RegionTree<E>,
        spilled: &EntitySet<Val<E>>,
        output: &mut OutputInner<E>,
    ) -> IResult<bool> {
        let is_candidate = |val: Val<E>| spilled.contains(val) && val.num_regs(input) == 1;

        for block in rpo.iter() {
            let input_block = input.func.block(block.with_repr32());
            for (i, succ) in input_block.successors().enumerate() {
                let succ = output.with_repr::<E, _>(succ)?;
                let args = input_block.successor_block_args(i);
                for (arg, param) in args.zip(input.func.block(succ.with_repr32()).params()) {
                    let arg = output.with_repr::<E, _>(arg)?;
                    let param = output.with_repr::<E, _>(param)?;
                    if arg == param
                        || !is_candidate(arg)
                        || !is_candidate(param)
                        || arg.reg_bank(input).size(input.machine)
                            != param.reg_bank(input).size(input.machine)
                    {
                        continue;
                    }
                    // Weigh the edge by the block its move would land in.
                    let holder = match input_block.len_successors() {
                        1 => block,
                        _ => succ,
                    };
                    let weight = block_weight(input, region_tree, holder);
                    self.affinities.push((weight, arg, param));
                    self.affine.insert(arg);
                    self.affine.insert(param);
                }
            }
        }
        Ok(!self.affinities.is_empty())
    }

    /// Take the set of values whose reservations need recording, to hand back
    /// with `restore_affine`.
    pub fn take_affine(&mut self) -> EntitySet<Val<E>> {
        core::mem::replace(&mut self.affine, EntitySet::new())
    }

    pub fn restore_affine(&mut self, affine: EntitySet<Val<E>>) {
        self.affine = affine;
    }

    /// Begin a reservation of `val` at `at`.
    pub fn open(&mut self, val: Val<E>, at: LivePoint<E>) {
        self.open_ranges[val] = Some(at);
        self.open.push(val);
    }

    /// End `val`'s open reservation, if any, at `at`.
    pub fn close(
        &mut self,
        output: &mut OutputInner<E>,
        val: Val<E>,
        at: LivePoint<E>,
    ) -> IResult<()> {
        match self.open_ranges[val].take() {
            Some(start) => self.add_range(output, val, start, at),
            None => Ok(()),
        }
    }

    /// End every open reservation at `at`, the end of the block.
    pub fn close_all(&mut self, output: &mut OutputInner<E>, at: LivePoint<E>) -> IResult<()> {
        let mut open = core::mem::take(&mut self.open);
        let result = open
            .drain(..)
            .try_for_each(|val| self.close(output, val, at));
        self.open = open;
        result
    }

    /// Add `[start, end)` to `val`'s reservations.
    fn add_range(
        &mut self,
        output: &mut OutputInner<E>,
        val: Val<E>,
        start: LivePoint<E>,
        end: LivePoint<E>,
    ) -> IResult<()> {
        if start >= end {
            return Ok(());
        }
        let Some(range) = SlotRange::try_new(self.num_ranges) else {
            return output.error(InternalError::EntityReprTooSmall);
        };
        self.num_ranges += 1;
        let one = IntervalSet::singleton(&mut self.range_arena, range, start, end);
        let set = match self.class_ranges[val] {
            None => one,
            // One value's reservations are in different blocks, so they never
            // overlap.
            Some(set) => set
                .try_union(&mut self.range_arena, one, &mut Fuel::new(u64::MAX))
                .expect("a value's reservations are disjoint"),
        };
        self.class_ranges[val] = Some(set);
        Ok(())
    }

    /// Order the affinities for `union_affinities`: heaviest edge first and,
    /// among equally hot edges, the parameter fed on more of them, since it
    /// saves more moves by keeping its arguments together. Stable, so that
    /// ties keep the walk's order.
    pub fn order_affinities(&mut self) {
        for &(weight, _, param) in &self.affinities {
            self.param_weight[param] += weight;
        }
        let param_weight = &self.param_weight;
        self.affinities.sort_by(|a, b| {
            b.0.total_cmp(&a.0)
                .then(param_weight[b.2].total_cmp(&param_weight[a.2]))
        });
    }

    /// Union each affinity's classes, in order, wherever their reservations
    /// stay disjoint.
    pub fn union_affinities(&mut self) {
        self.fuel = Fuel::safety_net(self.num_ranges);

        let mut affinities = core::mem::take(&mut self.affinities);
        for &(weight, arg, param) in &affinities {
            let a = self.sets.find(arg);
            let b = self.sets.find(param);
            if a == b {
                continue;
            }
            let (Some(set_a), Some(set_b)) = (self.class_ranges[a], self.class_ranges[b]) else {
                continue;
            };
            let mut fuel = Fuel::new(self.fuel);
            let result = set_a.try_union(&mut self.range_arena, set_b, &mut fuel);
            self.fuel = self.fuel.saturating_sub(fuel.spent());
            if let Ok(set) = result {
                let root = self.sets.union(a, b);
                let joined = self.class_weight[a] + self.class_weight[b] + weight;
                self.class_ranges[a] = None;
                self.class_ranges[b] = None;
                self.class_ranges[root] = Some(set);
                self.class_weight[root] = joined;
                trace!("spill slots: {arg:?} and {param:?} would rather share a slot");
            }
        }
        affinities.clear();
        self.affinities = affinities;

        // As much again for the walk.
        self.fuel = Fuel::safety_net(self.num_ranges);
    }

    /// The slot promised to `val`'s class, if any.
    pub fn slot(&mut self, val: Val<E>) -> Option<SpillSlot<E>> {
        let class = self.sets.find(val);
        self.class_slot[class]
    }

    /// Does keeping `val`'s class in one slot save any move?
    pub fn saves_moves(&mut self, val: Val<E>) -> bool {
        let class = self.sets.find(val);
        self.class_weight[class] > 0.0
    }

    /// Is `val`'s class still waiting for a promise it can be given: it has
    /// none yet, and has reservations to promise a slot over?
    pub fn awaits_promise(&mut self, val: Val<E>) -> bool {
        let class = self.sets.find(val);
        self.class_ranges[class].is_some()
    }

    /// Promise `slot` to `val`'s class if no promise already made over `slot`
    /// overlaps the class's reservations. Returns whether it did.
    pub fn try_promise(&mut self, val: Val<E>, slot: SpillSlot<E>) -> bool {
        let class = self.sets.find(val);
        let Some(ranges) = self.class_ranges[class] else {
            return false;
        };
        let merged = match self.slot_ranges[slot] {
            None => Some(ranges),
            Some(promised) => {
                let mut fuel = Fuel::new(self.fuel);
                let result = promised.try_union(&mut self.range_arena, ranges, &mut fuel);
                self.fuel = self.fuel.saturating_sub(fuel.spent());
                result.ok()
            }
        };
        let Some(merged) = merged else {
            return false;
        };
        self.slot_ranges[slot] = Some(merged);
        self.slot_weight[slot] += self.class_weight[class];
        self.class_ranges[class] = None;
        self.class_slot[class] = Some(slot);
        true
    }

    /// The first of `candidates` whose promises are worth the least.
    pub fn least_promised(
        &self,
        candidates: impl Iterator<Item = SpillSlot<E>>,
    ) -> Option<SpillSlot<E>> {
        let mut best: Option<(SpillSlot<E>, f64)> = None;
        for slot in candidates {
            let weight = self.slot_weight[slot];
            if best.is_none_or(|(_, best_weight)| weight < best_weight) {
                best = Some((slot, weight));
                // Weights are never negative, so nothing beats an unpromised
                // slot.
                if weight == 0.0 {
                    break;
                }
            }
        }
        best.map(|(slot, _)| slot)
    }

    /// The root of `val`'s class.
    #[cfg(test)]
    pub fn class_of(&self, val: Val<E>) -> Val<E> {
        self.sets.find_without_path_compression(val)
    }
}

/// How often `block` runs relative to the function's entry: 10x per enclosing
/// loop, and a twentieth for a cold block.
pub(super) fn block_weight<E>(
    input: &Input<'_, impl InputFunction>,
    region_tree: &RegionTree<E>,
    block: Block<E>,
) -> f64
where
    E: EntityRepr,
{
    let mut weight = 1.0;
    for _ in 0..block.loop_depth(region_tree) {
        weight *= 10.0;
    }
    if block.frequency(input.func).is_cold() {
        weight *= 0.05;
    }
    weight
}
