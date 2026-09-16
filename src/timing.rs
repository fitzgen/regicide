//! Pass-timing infrastructure.

use core::fmt::Display;
#[cfg(feature = "timing")]
use std::time::Instant;

pub struct Timing<T>
where
    T: Display,
{
    #[cfg(feature = "timing")]
    start: Instant,
    #[cfg(feature = "timing")]
    label: T,
    #[cfg(not(feature = "timing"))]
    _phantom: core::marker::PhantomData<fn() -> T>,
}

impl<T> Timing<T>
where
    T: Display,
{
    #[inline]
    pub fn new(label: T) -> Self {
        if cfg!(feature = "timing") {
            crate::trace!("Start timing: {label}");
        }

        Self {
            #[cfg(feature = "timing")]
            start: Instant::now(),
            #[cfg(feature = "timing")]
            label,
            #[cfg(not(feature = "timing"))]
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T> Drop for Timing<T>
where
    T: Display,
{
    fn drop(&mut self) {
        #[cfg(feature = "timing")]
        {
            let elapsed = self.start.elapsed();
            let millis = (elapsed.as_millis() as f64) + (elapsed.as_micros() as f64 * 1000.0);
            crate::trace!("Finish timing: {}: {millis:02}ms", self.label);
        }
    }
}
