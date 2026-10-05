use crate::ir::*;
use axum::{
    extract::State,
    response::{Html, IntoResponse},
    routing::{get, post},
    Json, Router,
};
use canonical_core::core::*;
use canonical_core::memory::*;
use canonical_core::prover::Prover;
use canonical_core::search::*;
use canonical_core::independence::split;
use serde::Deserialize;
use serde_json::json;
use std::sync::{Arc, Mutex, MutexGuard, OnceLock};
use std::time::Duration;
use std::mem;
use canonical_core::independence::collect_unassigned;

/// HTML for the refinement interface.
const HTML: &str = include_str!("../static/index.html");

/// The maximum number of forced moves that can be made on the user's behalf at one time.
const AUTOFILL_LIMIT: u32 = 30;

/// The global state of the backend.
pub static GLOBAL_STATE: OnceLock<Arc<Mutex<AppState>>> = OnceLock::new();

fn lock(state: &Arc<Mutex<AppState>>) -> MutexGuard<'_, AppState> {
    state.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// When there is no server running, start an Axum server with the given AppState.
pub async fn start_server(state: AppState) {
    let state = Arc::new(Mutex::new(state));

    let app = Router::new()
        .route("/", get(index))
        .route("/assign", post(assign))
        .route("/undo", post(undo))
        .route("/redo", post(redo))
        .route("/reset", post(reset))
        .route("/term", post(term))
        .route("/canonical", post(canonical))
        .route("/canonical1", post(canonical1))
        .route("/set", post(set))
        .with_state(state.clone());

    let _ = GLOBAL_STATE.set(state);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

/// Internal state for the Axum webserver.
pub struct AppState {
    /// The prover for the term currently being displayed.
    pub current: Prover,
    /// The undo stack.
    pub undo: Vec<Prover>,
    /// The redo stack.
    pub redo: Vec<Prover>,
    /// Whether to automatically make forced moves. 
    pub autofill: bool,
    pub constraints: bool,

    // For ownership purposes.
    pub _owned_tb: S<TypeBase>,
    pub _owned_bind: S<Bind>
}

/// Sent from JS to represent an assignment.
#[derive(Deserialize, Debug)]
struct Assign {
    /// Hashcode of the metavariable to assign.
    meta_id: usize,
    // DeBruijnIndex
    debruijn: u32,
    index: usize,
    def: bool
}

/// Data structure sent when Solve1 is pressed.
#[derive(Deserialize)]
struct Solve1 {
    /// Hashcode of the metavariable to be solved.
    meta_id: usize
}

/// Retrieve the HTML file.
async fn index() -> impl IntoResponse {
    Html(HTML)
}

/// Get the current term as HTML, and next metavariable.
async fn term(State(state): State<Arc<Mutex<AppState>>>) -> Json<serde_json::Value> {
    let state = lock(&state);
    let meta = state.current.meta.downgrade();
    let mut owned_linked = Vec::new();
    let term = IRSpine::from_body::<false>(Term { base: meta.clone(), es: meta.borrow().gamma.clone() }.whnf::<false, ()>(&mut owned_linked, &mut ()), true);
    let html = term.to_string();

    let mut unassigned = Vec::new();
    collect_unassigned(state.current.meta.downgrade(), &mut unassigned);
    let components = split(&unassigned);
    let next = components.first()
        .map(|c| c.next.meta.borrow() as *const Meta as usize);
    let components : Vec<Vec<String>> = components.iter().map(|c|
        std::iter::once(&c.next.meta).chain(c.unassigned.iter()).map(|m|
            m.borrow().typ.as_ref().unwrap().2.borrow().name.clone()
        ).collect()
    ).collect();
    let html = format!("{}\n\n{:?}", html, components);

    return Json(json!({
        "html": html,
        "next": next,
        "undo": !state.undo.is_empty(),
        "redo": !state.redo.is_empty(),
        "autofill": state.autofill,
        "constraints": state.constraints
    }));
}

/// Perform the assignment on the prover in the state. 
async fn assign(
    State(state): State<Arc<Mutex<AppState>>>,
    Json(assign): Json<Assign>,
) -> Json<serde_json::Value> {
    let mut state = lock(&state);

    let index = if assign.def {
        Index::Let(assign.index)
    } else {
        Index::Param(assign.index)
    };
    let mut db = DeBruijnIndex(DeBruijn(assign.debruijn), index);

    let current = state.current.meta.downgrade();
    let mut new = state.current.clone();
    let Some(mut meta) = find_with_id(current, new.meta.downgrade(), assign.meta_id) else {
        return Json(json!({ "error": "Stale metavariable" }));
    };

    let mut i = 0;

    while i < AUTOFILL_LIMIT {
        if !new.refine(meta, db) {
            return Json(json!({ "error": "Invalid assignment" }));
        }

        if !state.autofill {
            break;
        }
        
        if let Some((found, found_db)) = find_autofill(new.meta.downgrade()) {
            meta = found;
            db = found_db;
        } else {
            break;
        }

        i += 1;
    }

    let prev = mem::replace(&mut state.current, new);
    state.redo.clear();
    state.undo.push(prev);

    Json(json!({}))
}

/// Undo an assignment.
async fn undo(State(state): State<Arc<Mutex<AppState>>>) -> Json<serde_json::Value> {
    let mut state = lock(&state);
    
    if let Some(prev) = state.undo.pop() {
        let new = mem::replace(&mut state.current, prev);
        state.redo.push(new);
    }
    Json(json!({}))
}

/// Redo an assignment.
async fn redo(State(state): State<Arc<Mutex<AppState>>>) -> Json<serde_json::Value> {
    let mut state = lock(&state);
    
    if let Some(prev) = state.redo.pop() {
        let new = mem::replace(&mut state.current, prev);
        state.undo.push(new);
    }
    Json(json!({}))
}

/// Reset the prover to a single metavariable.
async fn reset(State(state): State<Arc<Mutex<AppState>>>) -> Json<serde_json::Value> {
    let mut state = lock(&state);
    state.undo = Vec::new();
    state.redo = Vec::new();
    state.current = Prover::new(state._owned_tb.downgrade(), state._owned_bind.downgrade());
    Json(json!({}))
}

/// Attempt to complete the proof with Canonical.
async fn canonical(State(state): State<Arc<Mutex<AppState>>>) -> Json<serde_json::Value> {
    let mut state = lock(&state);
    let prover = state.current.clone();
    let next_root = prover.meta.downgrade();
    if let Some(term) = canonical_simple(prover, next_root) {
        let prev = mem::replace(&mut state.current, term);
        state.redo.clear();
        state.undo.push(prev);
    }
    Json(json!({}))
}

/// Attempt to complete only the specified subtree with Canonical.
async fn canonical1(State(state): State<Arc<Mutex<AppState>>>, Json(solve1) : Json<Solve1>) -> Json<serde_json::Value> {
    let mut state = lock(&state);
    let current = state.current.meta.downgrade();
    let prover = state.current.clone();
    let Some(next_root) = find_with_id(current, prover.meta.downgrade(), solve1.meta_id) else {
        return Json(json!({ "error": "Stale metavariable" }));
    };
    if let Some(term) = canonical_simple(prover, next_root) {
        let prev = mem::replace(&mut state.current, term);
        state.redo.clear();
        state.undo.push(prev);
    }
    Json(json!({}))
}

/// Run Canonical for up to one second below the existing assignments.
fn canonical_simple(mut prover: Prover, next_root: W<Meta>) -> Option<Prover> {
    if prover.complete(next_root, Duration::from_secs(1)) { Some(prover) } else { None }
}

/// Find the selected metavariable in the corresponding position of the clone.
fn find_with_id(meta: W<Meta>, copy: W<Meta>, id: usize) -> Option<W<Meta>> {
    match &meta.borrow().assignment {
        None => {
            if (meta.borrow() as *const Meta as usize) == id {
                Some(copy)
            } else {
                None
            }
        }
        Some(assignment) => {
            for (arg, copied) in assignment.args.iter().zip(&copy.borrow().assignment.as_ref()?.args) {
                if let Some(found) = find_with_id(arg.downgrade(), copied.downgrade(), id) {
                    return Some(found);
                }
            }
            None
        }
    }
}

/// If there exists a metavariable with a single domain element, 
/// return that metavariable and the `DeBruijnIndex` of the variable.
fn find_autofill(meta: W<Meta>) -> Option<(W<Meta>, DeBruijnIndex)> {
    match &meta.borrow().assignment {
        None => {
            let domain: Vec<(DeBruijnIndex, W<Linked>)> = meta.borrow().gamma.iter()
            .filter(|(db, linked, _)| {
                test(db.clone(), linked.clone(), meta.clone()).is_some_and(|o| o.is_some())
            }).map(|(db, linked, _)| (db, linked)).collect();

            if domain.len() == 1 {
                Some((meta, domain[0].0))
            } else {
                None
            }
        }
        Some(assignment) => {
            for arg in assignment.args.iter() {
                if let Some(found) = find_autofill(arg.downgrade()) {
                    return Some(found);
                }
            }
            None
        }
    }
}

/// A key-value pair, for setting options through Axum.
#[derive(Deserialize)]
struct KV {
    key: String,
    value: bool
}

/// Sets the given option flag.
async fn set(State(state): State<Arc<Mutex<AppState>>>, Json(kv) : Json<KV>) -> Json<serde_json::Value> {
    let mut state = lock(&state);

    if kv.key == "autofill" {
        state.autofill = kv.value;
    } else if kv.key == "constraints" {
        state.constraints = kv.value;
    }
    Json(json!({}))
}

