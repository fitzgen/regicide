//! Counts for various events and such.

use core::fmt;

pub struct Count {
    #[cfg(feature = "trace-log")]
    count: u64,
}

impl fmt::Debug for Count {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
}

impl Counts {
    pub const fn new() -> Self {
        Self {
            sccs: Count::new(),
            regions: Count::new(),
            liveness_iterations: Count::new(),
            live_spans: Count::new(),
            uses: Count::new(),
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
        } = self;
        sccs.is_reset()
            && regions.is_reset()
            && liveness_iterations.is_reset()
            && live_spans.is_reset()
            && uses.is_reset()
    }
}
