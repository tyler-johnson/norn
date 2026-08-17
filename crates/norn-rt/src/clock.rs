//! Time, real or simulated.
//!
//! A virtual clock is what makes a scheduling test a golden file rather than a race: when nothing
//! is runnable and only timers are pending, the runtime jumps the clock to the next deadline
//! instead of sleeping. Timer and cancellation tests become instant and deterministic. This is the
//! "virtual clocks, deterministic event injection" of `DESIGN.md` §12, arriving early because it is
//! what makes M2 testable at all.

use std::time::{Duration, Instant};

/// Milliseconds since the runtime started. Absolute wall-clock time is not something the language
/// exposes yet, and a monotonic offset is all the scheduler needs.
pub type Millis = u64;

pub enum Clock {
    Real { start: Instant },
    Virtual { now: Millis },
}

impl Clock {
    pub fn real() -> Clock {
        Clock::Real {
            start: Instant::now(),
        }
    }

    pub fn simulated() -> Clock {
        Clock::Virtual { now: 0 }
    }

    pub fn is_virtual(&self) -> bool {
        matches!(self, Clock::Virtual { .. })
    }

    pub fn now(&self) -> Millis {
        match self {
            Clock::Real { start } => start.elapsed().as_millis() as Millis,
            Clock::Virtual { now } => *now,
        }
    }

    /// Move time forward to `deadline`. A real clock sleeps; a virtual one simply arrives.
    ///
    /// The return value says whether the trace should record a jump: for a virtual clock the jump
    /// *is* the event, while a real clock only did what time does on its own.
    pub fn wait_until(&mut self, deadline: Millis) -> bool {
        match self {
            Clock::Real { start } => {
                let now = start.elapsed().as_millis() as Millis;
                if now < deadline {
                    std::thread::sleep(Duration::from_millis(deadline - now));
                }
                false
            }
            Clock::Virtual { now } => {
                if *now < deadline {
                    *now = deadline;
                    true
                } else {
                    false
                }
            }
        }
    }
}
