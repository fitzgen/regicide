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

    pub fn reset(&mut self) {
        #[cfg(feature = "trace-log")]
        {
            let Self { count } = self;
            *count = 0;
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
    pub live_ranges: Count,
}

impl Counts {
    pub const fn new() -> Self {
        Self {
            sccs: Count::new(),
            regions: Count::new(),
            live_ranges: Count::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self {
            sccs,
            regions,
            live_ranges,
        } = self;
        *sccs = Count::new();
        *regions = Count::new();
        *live_ranges = Count::new();
    }

    pub fn is_reset(&self) -> bool {
        let Self {
            sccs,
            regions,
            live_ranges,
        } = self;
        sccs.is_reset() && regions.is_reset() && live_ranges.is_reset()
    }
}
