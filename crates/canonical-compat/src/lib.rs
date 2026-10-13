use canonical_core::core::*;
use canonical_core::prover::Prover;
pub mod ir;
pub mod refine;
pub mod reduction;
pub mod ab;
use ir::*;
use canonical_core::stats::STEP_COUNT;
use std::time::SystemTime;
// use canonical_core::search::EXPERIMENT;
// use std::sync::atomic::Ordering;
// use crate::refine::{AppState, start_server};

/// Manually construct an IRExpr body.
#[allow(unused_macros)]
macro_rules! t {
    ($s : expr $(, $arg : expr)*) => {
        IRExpr {
            params: vec![],
            lets: vec![],
            spine: IRSpine {
                head: $s.to_string(),
                args: vec![$($arg),*],
                premise_rules: vec![]
            },
            goal_rules: vec![]
        }
    };
}

/// Manually construct a lambda IRExpr.
#[allow(unused_macros)]
macro_rules! l {
    ($params : expr, $s : expr $(, $arg : expr)*) => {
        IRExpr {
            params: $params.iter().map(|name| IRDecl { name: name.to_string(), typ: None, equations: vec![] }).collect(),
            lets: vec![],
            spine: IRSpine {
                head: $s.to_string(),
                args: vec![$($arg),*],
                premise_rules: vec![]
            },
            goal_rules: vec![]
        }
    };
}

/// Manually construct an IRExpr codomain.
#[allow(unused_macros)]
macro_rules! T {
    () => {
        None as Option<IRExpr>
    };
    ($s : expr $(, $arg : expr)*) => {
        Some(t!($s $(, $arg)*))
    };
}

/// Manually construct a Pi IRExpr.
#[allow(unused_macros)]
macro_rules! P {
    ($params : expr, $s : expr $(, $arg : expr)*) => {
        Some(IRExpr {
            params: $params.into_iter().map(|(name, typ)| IRDecl { name: name.to_string(), typ, equations: vec![] }).collect(),
            lets: vec![],
            spine: IRSpine {
                head: $s.to_string(),
                args: vec![$($arg),*],
                premise_rules: vec![]
            },
            goal_rules: vec![]
        })
    };
}


#[tokio::main]
async fn main() {
    // Entrypoint for CLI: A/B test the `EXPERIMENT` flag on random examples from `Results/`.
    // Usage: `canonical-compat [count] [seed]` (defaults: 30 examples, time-based seed).
    // let count = std::env::args().nth(1).and_then(|arg| arg.parse().ok()).unwrap_or(30);
    // let seed = std::env::args().nth(2).and_then(|arg| arg.parse().ok());
    // ab::ab_test(count, seed, |enabled| EXPERIMENT.store(enabled, Ordering::Release));

    let problem = IRDecl::load("lean/debug.json".to_string());
    let (decl, tokens) = problem.to_problem();
    canonical_core::ai::start(&tokens);

    // let state = AppState {
    //     current: Prover::new(decl.downgrade()).meta,
    //     undo: Vec::new(),
    //     redo: Vec::new(),
    //     autofill: true,
    //     constraints: false,
    //     _owned_decl: decl
    // };

    // start_server(state).await;

    // Print step count each second.
    std::thread::spawn(move || {
        let mut prev = 0;
        loop {
            std::thread::sleep(std::time::Duration::from_secs(1));
            let count = STEP_COUNT.load(std::sync::atomic::Ordering::Relaxed);
            println!("total: {}", count);
            println!("t/s: {}", count - prev);
            prev = count;
        }
    });
    
    let now = SystemTime::now();
    Prover::new(decl.downgrade()).prove(&|term: Term| {
        let mut owned_linked = Vec::new();
        println!("{}", now.elapsed().unwrap().as_secs_f32());
        println!("{}", IRSpine::from_body::<false>(term.whnf::<false, ()>(&mut owned_linked, &mut (), false), false));
        std::process::exit(0);
    }, true);
}