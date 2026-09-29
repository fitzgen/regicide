//! Counts for various events and such.

use core::fmt;

pub struct Count {
    #[cfg(feature = "trace-log")]
    count: u64,
}

impl fmt::Debug for Count {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let _ = &f;
        #[cfg(feature = "trace-log")]
        fmt::Debug::fmt(&self.count, f)?;
        Ok(())
    }
}

impl core::ops::AddAssign<u64> for Count {
    fn add_assign(&mut self, rhs: u64) {
        let _ = &rhs;
        #[cfg(feature = "trace-log")]
        {
            self.count += rhs;
        }
    }
}

impl core::ops::AddAssign<usize> for Count {
    fn add_assign(&mut self, rhs: usize) {
        let _ = &rhs;
        #[cfg(feature = "trace-log")]
        {
            self.count += u64::try_from(rhs).unwrap();
        }
    }
}

impl Count {
    pub const fn new() -> Self {
        Self {
            #[cfg(feature = "trace-log")]
            count: 0,
        }
    }

    pub fn inc(&mut self) {
        *self += 1u64;
    }

    pub fn is_reset(&self) -> bool {
        #[cfg(not(feature = "trace-log"))]
        return true;
        #[cfg(feature = "trace-log")]
        {
            let Self { count } = self;
            *count == 0
        }
    }
}

#[derive(Debug)]
pub struct Counts {
    pub sccs: Count,
    pub regions: Count,
    pub liveness_iterations: Count,
    pub live_spans: Count,
    pub uses: Count,
    pub eager_splits: Count,
    pub overwrite_splits: Count,
    pub bundles: Count,
    pub queue_pops: Count,
    pub preferred_assignments: Count,
    pub non_preferred_assignments: Count,
    pub evictions: Count,
    pub split_between_spans: Count,
    pub split_between_spans_failed: Count,
    pub split_within_span: Count,
    pub split_within_span_failed: Count,
    pub split_into_minimal_or_spill: Count,
    pub spilled_bundles: Count,
    pub early_half_reloads: Count,
    pub rematerialized_bundles: Count,
    pub spilled_values: Count,
    pub spill_slots: Count,
    pub spill_slot_assignments: Count,
    pub final_live_spans: Count,
    pub final_bundles: Count,
    pub spills_placed: Count,
    pub half_move_sources: Count,
    pub half_move_dests: Count,
    pub moves_emitted: Count,
    pub remats_emitted: Count,
    pub moves_eliminated: Count,
    pub remats_eliminated: Count,
    pub critical_edge_edits: Count,
    pub move_cycles_broken: Count,
    pub cycles_parked_on_the_stack: Count,
    pub stack_to_stack_moves: Count,
    pub borrowed_scratch_regs: Count,
    pub scratch_reg_homes_reused: Count,
    pub emergency_spill_slots: Count,
}

impl Counts {
    pub const fn new() -> Self {
        Self {
            sccs: Count::new(),
            regions: Count::new(),
            liveness_iterations: Count::new(),
            live_spans: Count::new(),
            uses: Count::new(),
            eager_splits: Count::new(),
            overwrite_splits: Count::new(),
            bundles: Count::new(),
            queue_pops: Count::new(),
            preferred_assignments: Count::new(),
            non_preferred_assignments: Count::new(),
            evictions: Count::new(),
            split_between_spans: Count::new(),
            split_between_spans_failed: Count::new(),
            split_within_span: Count::new(),
            split_within_span_failed: Count::new(),
            split_into_minimal_or_spill: Count::new(),
            spilled_bundles: Count::new(),
            early_half_reloads: Count::new(),
            rematerialized_bundles: Count::new(),
            spilled_values: Count::new(),
            spill_slots: Count::new(),
            spill_slot_assignments: Count::new(),
            final_live_spans: Count::new(),
            final_bundles: Count::new(),
            spills_placed: Count::new(),
            half_move_sources: Count::new(),
            half_move_dests: Count::new(),
            moves_emitted: Count::new(),
            remats_emitted: Count::new(),
            moves_eliminated: Count::new(),
            remats_eliminated: Count::new(),
            critical_edge_edits: Count::new(),
            move_cycles_broken: Count::new(),
            cycles_parked_on_the_stack: Count::new(),
            stack_to_stack_moves: Count::new(),
            borrowed_scratch_regs: Count::new(),
            scratch_reg_homes_reused: Count::new(),
            emergency_spill_slots: Count::new(),
        }
    }

    pub fn reset(&mut self) {
        *self = Self::new();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            sccs,
            regions,
            liveness_iterations,
            live_spans,
            uses,
            eager_splits,
            overwrite_splits,
            bundles,
            queue_pops,
            preferred_assignments,
            non_preferred_assignments,
            evictions,
            split_between_spans,
            split_between_spans_failed,
            split_within_span,
            split_within_span_failed,
            split_into_minimal_or_spill,
            spilled_bundles,
            early_half_reloads,
            rematerialized_bundles,
            spilled_values,
            spill_slots,
            spill_slot_assignments,
            final_live_spans,
            final_bundles,
            spills_placed,
            half_move_sources,
            half_move_dests,
            moves_emitted,
            remats_emitted,
            moves_eliminated,
            remats_eliminated,
            critical_edge_edits: critical_edge_moves,
            move_cycles_broken,
            cycles_parked_on_the_stack,
            stack_to_stack_moves,
            borrowed_scratch_regs,
            scratch_reg_homes_reused,
            emergency_spill_slots,
        } = self;
        sccs.is_reset()
            && regions.is_reset()
            && liveness_iterations.is_reset()
            && live_spans.is_reset()
            && uses.is_reset()
            && eager_splits.is_reset()
            && overwrite_splits.is_reset()
            && bundles.is_reset()
            && queue_pops.is_reset()
            && preferred_assignments.is_reset()
            && non_preferred_assignments.is_reset()
            && evictions.is_reset()
            && split_between_spans.is_reset()
            && split_between_spans_failed.is_reset()
            && split_within_span.is_reset()
            && split_within_span_failed.is_reset()
            && split_into_minimal_or_spill.is_reset()
            && spilled_bundles.is_reset()
            && early_half_reloads.is_reset()
            && rematerialized_bundles.is_reset()
            && spilled_values.is_reset()
            && spill_slots.is_reset()
            && spill_slot_assignments.is_reset()
            && final_live_spans.is_reset()
            && final_bundles.is_reset()
            && spills_placed.is_reset()
            && half_move_sources.is_reset()
            && half_move_dests.is_reset()
            && moves_emitted.is_reset()
            && remats_emitted.is_reset()
            && moves_eliminated.is_reset()
            && remats_eliminated.is_reset()
            && critical_edge_moves.is_reset()
            && move_cycles_broken.is_reset()
            && cycles_parked_on_the_stack.is_reset()
            && stack_to_stack_moves.is_reset()
            && borrowed_scratch_regs.is_reset()
            && scratch_reg_homes_reused.is_reset()
            && emergency_spill_slots.is_reset()
    }
}
