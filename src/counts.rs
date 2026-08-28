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
    pub final_live_spans: Count,
    pub final_bundles: Count,
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
            final_live_spans: Count::new(),
            final_bundles: Count::new(),
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
            final_live_spans,
            final_bundles,
        } = self;
        sccs.is_reset()
            && regions.is_reset()
            && liveness_iterations.is_reset()
            && live_spans.is_reset()
            && uses.is_reset()
            && eager_splits.is_reset()
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
            && final_live_spans.is_reset()
            && final_bundles.is_reset()
    }
}
