use crate::ir::IRType;
use serde::Deserialize;
use std::collections::HashMap;
use std::fs::File;
use canonical_core::core::*;
use canonical_core::memory::S;
use canonical_core::prover::Prover;
use canonical_core::search::*;
use canonical_core::stats::{LIMIT, STEP_COUNT};
use std::fs;
use std::panic::{self, AssertUnwindSafe};
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// The step limit shared by both runs of each example.
const STEP_LIMIT: u32 = 10_000_000;

/// The format of the examples in `Results/` (from CanonicalData.tar).
#[derive(Deserialize)]
struct Example {
    problem: IRType,
    #[allow(dead_code)]
    unifications: HashMap<String, HashMap<String, u32>>,
}

impl Example {
    fn load(path: &str) -> Example {
        rmp_serde::decode::from_read(File::open(path).unwrap()).unwrap()
    }
}

/// A/B test `configure(false)` against `configure(true)` on `n` random examples from `Results/`.
/// Pass the same `seed` to rerun on the same set of examples.
pub fn ab_test<F: Fn(bool)>(n: usize, seed: Option<u64>, configure: F) {
    let seed = seed.unwrap_or_else(|| SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos() as u64);
    println!("seed: {seed}");
    watchdog();
    LIMIT.store(STEP_LIMIT, Ordering::Release);

    let files = sample_files("Results", n, seed);
    let mut solved = [0u32; 2];
    let mut log_ratio_sum = 0.0;
    let mut both_solved = 0;

    println!("name, A steps, A solved, B steps, B solved");
    for path in &files {
        let name = path.file_stem().unwrap().to_str().unwrap();
        let results = panic::catch_unwind(AssertUnwindSafe(|| {
            let problem = Example::load(path.to_str().unwrap()).problem;
            let tb = S::new(problem.to_type(&ES::new(), Polarity::Goal).0);
            let problem_bind = S::new(Bind::new("proof".to_string(), Polarity::Goal));
            [false, true].map(|enabled| {
                configure(enabled);
                let mut prover = Prover::new(tb.downgrade(), problem_bind.downgrade());
                let solved = AtomicBool::new(false);
                let steps = prover.prove(&|_| {
                    solved.store(true, Ordering::Relaxed);
                    RUN.store(false, Ordering::Relaxed);
                }, false).0.steps;
                (steps, solved.into_inner())
            })
        }));
        let Ok([(a_steps, a_solved), (b_steps, b_solved)]) = results else {
            println!("{name}, error, , , ");
            continue;
        };

        println!("{name}, {a_steps}, {a_solved}, {b_steps}, {b_solved}");
        solved[0] += a_solved as u32;
        solved[1] += b_solved as u32;
        if a_solved && b_solved {
            both_solved += 1;
            log_ratio_sum += (a_steps.max(1) as f64 / b_steps.max(1) as f64).ln();
        }
    }

    println!("A solved: {}/{}", solved[0], files.len());
    println!("B solved: {}/{}", solved[1], files.len());
    if both_solved > 0 {
        println!("geometric mean speedup (A steps / B steps, over {both_solved} solved by both): {}",
            (log_ratio_sum / both_solved as f64).exp());
    }
}

/// Choose `n` random `.bin` files from `dir`, deterministically given `seed`.
fn sample_files(dir: &str, n: usize, seed: u64) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = fs::read_dir(dir).unwrap()
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|path| path.extension().and_then(|e| e.to_str()) == Some("bin"))
        .collect();
    files.sort();

    let mut state = seed | 1;
    let mut rng = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let n = n.min(files.len());
    for i in 0..n {
        let j = i + rng() as usize % (files.len() - i);
        files.swap(i, j);
    }
    files.truncate(n);
    files
}

/// Cancel the ongoing search if no steps occur for two consecutive seconds.
fn watchdog() {
    std::thread::spawn(|| {
        let mut prev = u32::MAX;
        let mut stalled = 0;
        loop {
            std::thread::sleep(Duration::from_secs(1));
            let count = STEP_COUNT.load(Ordering::Relaxed);
            stalled = if count == prev && RUN.load(Ordering::Relaxed) { stalled + 1 } else { 0 };
            if stalled >= 2 {
                eprintln!("watchdog: search stalled, cancelling");
                RUN.store(false, Ordering::Relaxed);
            }
            prev = count;
        }
    });
}
