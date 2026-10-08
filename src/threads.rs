//! Work shared out among threads and given back in order.
//!
//! A test that runs many cases independent of each other runs them side by
//! side. It uses as many threads as `PARLEY_THREADS` says where that is
//! set, so that a profile shows one thread doing all of the work, and one
//! for each core otherwise.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

/// How many threads work is shared among.
pub fn threads() -> usize {
    match std::env::var("PARLEY_THREADS") {
        Ok(text) => text
            .parse::<usize>()
            .ok()
            .filter(|&n| n > 0)
            .unwrap_or_else(|| {
                panic!("PARLEY_THREADS is {text:?}, not a number of threads")
            }),
        Err(_) => std::thread::available_parallelism().map_or(1, |n| n.get()),
    }
}

/// `run` over every item, on `threads()` threads at once, given back in the
/// items' order.
///
/// Each thread first makes a state of its own with `init`, for what cannot
/// be shared between threads, and hands it to `run` with each item it takes.
/// A thread takes the next item not yet taken, which keeps every thread busy
/// when some items cost far more than others.
pub fn in_order<I: Sync, S, T: Send>(
    items: &[I],
    init: impl Fn() -> S + Sync,
    run: impl Fn(&mut S, &I) -> T + Sync,
) -> Vec<T> {
    let next = AtomicUsize::new(0);
    let done: Mutex<Vec<Option<T>>> = Mutex::new(items.iter().map(|_| None).collect());
    std::thread::scope(|scope| {
        for _ in 0..threads().min(items.len()) {
            scope.spawn(|| {
                let mut state = init();
                loop {
                    let i = next.fetch_add(1, Ordering::Relaxed);
                    let Some(item) = items.get(i) else { break };
                    let result = run(&mut state, item);
                    done.lock().expect("no thread panicked holding it")[i] =
                        Some(result);
                }
            });
        }
    });
    done.into_inner()
        .expect("no thread panicked holding it")
        .into_iter()
        .map(|r| r.expect("every item was run"))
        .collect()
}
