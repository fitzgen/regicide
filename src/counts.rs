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

impl<T> core::ops::AddAssign<T> for Count
where
    T: Into<u64>,
{
    fn add_assign(&mut self, rhs: T) {
        let _ = &rhs;
        #[cfg(feature = "trace-log")]
        {
            let rhs = rhs.into();
            self.count += rhs;
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
    pub live_ranges: Count,
}

impl Counts {
    pub const fn new() -> Self {
        Self {
            live_ranges: Count::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self { live_ranges } = self;
        *live_ranges = Count::new();
    }

    pub fn is_reset(&self) -> bool {
        let Self { live_ranges } = self;
        live_ranges.is_reset()
    }
}
