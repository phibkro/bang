// WASI-0.3 async spike driver — Q(conc-3)/G8.
//
// Times an async-lifted component export (WASI 0.3 async ABI: canon lift ...
// async (callback ...), driven by the wasmtime host event loop) against a
// sync-lifted export returning the same value. Mirrors the G2 driver's
// engine-pinned, compile-once style: the engine is built ONCE and each
// component compiled ONCE; only the call under test is timed.
//
// Usage:
//   wasi-async-driver call-sync  <component.wasm> <export> <iters>
//   wasi-async-driver call-async <component.wasm> <export> <iters>
//
// Both call the same u32-returning export; the difference in µs/call is the
// async lift/lower bookkeeping (task alloc, event-loop drive, task.return,
// subtask teardown) on top of the shared canonical-ABI floor.

use std::env;
use std::time::Instant;
use wasmtime::component::{Component, Linker, Val};
use wasmtime::{Config, Engine, Store};

fn engine(async_support: bool) -> Engine {
    let mut cfg = Config::new();
    cfg.wasm_component_model(true);
    if async_support {
        cfg.async_support(true);
        cfg.wasm_component_model_async(true);
    }
    Engine::new(&cfg).expect("engine")
}

// Sync path: a plain blocking component call (no async runtime).
fn call_sync(path: &str, export: &str, iters: u64) {
    let engine = engine(false);
    let bytes = std::fs::read(path).expect("read component");
    let component = Component::new(&engine, &bytes).expect("compile component");
    let linker: Linker<()> = Linker::new(&engine);
    let mut store = Store::new(&engine, ());
    let inst = linker.instantiate(&mut store, &component).expect("inst");
    let func = inst
        .get_func(&mut store, export)
        .unwrap_or_else(|| panic!("no export {export}"));

    let args: Vec<Val> = vec![];
    let mut results = vec![Val::U32(0)];

    for _ in 0..100 {
        func.call(&mut store, &args, &mut results).expect("warmup");
    }
    let t = Instant::now();
    for _ in 0..iters {
        func.call(&mut store, &args, &mut results).expect("call");
        std::hint::black_box(&results);
    }
    let ns = t.elapsed().as_nanos();
    println!(
        "call-sync\t{}\tus_per_call\t{:.5}\t(n={})\tresult={:?}",
        export,
        ns as f64 / iters as f64 / 1000.0,
        iters,
        results[0]
    );
}

// Async path: drive the export through the host event loop via call_async on a
// current-thread Tokio runtime. This is the honest WASI-0.3 async call: the
// runtime allocates a task, runs the async-lifted export, the guest calls
// task.return, and the callback reports EXIT.
fn call_async(path: &str, export: &str, iters: u64) {
    let rt = tokio::runtime::Builder::new_current_thread()
        .build()
        .expect("tokio rt");
    rt.block_on(async move {
        let engine = engine(true);
        let bytes = std::fs::read(path).expect("read component");
        let component = Component::new(&engine, &bytes).expect("compile component");
        let linker: Linker<()> = Linker::new(&engine);
        let mut store = Store::new(&engine, ());
        let inst = linker
            .instantiate_async(&mut store, &component)
            .await
            .expect("inst");
        let func = inst
            .get_func(&mut store, export)
            .unwrap_or_else(|| panic!("no export {export}"));

        let args: Vec<Val> = vec![];
        let mut results = vec![Val::U32(0)];

        for _ in 0..100 {
            func.call_async(&mut store, &args, &mut results)
                .await
                .expect("warmup");
        }
        let t = Instant::now();
        for _ in 0..iters {
            func.call_async(&mut store, &args, &mut results)
                .await
                .expect("call");
            std::hint::black_box(&results);
        }
        let ns = t.elapsed().as_nanos();
        println!(
            "call-async\t{}\tus_per_call\t{:.5}\t(n={})\tresult={:?}",
            export,
            ns as f64 / iters as f64 / 1000.0,
            iters,
            results[0]
        );
    });
}

fn main() {
    let a: Vec<String> = env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("call-sync") => call_sync(&a[2], &a[3], a[4].parse().unwrap()),
        Some("call-async") => call_async(&a[2], &a[3], a[4].parse().unwrap()),
        _ => {
            eprintln!("usage: wasi-async-driver call-sync|call-async <c.wasm> <export> <iters>");
            std::process::exit(2);
        }
    }
}
