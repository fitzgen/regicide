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
        // `log::debug!` rather than `crate::trace!`: the latter compiles to
        // nothing without `trace-log`, which would make a build carrying
        // `timing` alone log nothing at all. Pass shares have to be
        // measurable on a build shaped like production, which does not run
        // the trace logging.
        if cfg!(feature = "timing") {
            ::log::debug!("Start timing: {label}");
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
            let millis = elapsed.as_secs_f64() * 1000.0;
            ::log::debug!("Finish timing: {}: {millis:.3}ms", self.label);
        }
    }
}
