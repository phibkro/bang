// G2 measurement driver — component instantiation cost + canonical-ABI copy tax.
//
// Usage:
//   g2-driver instantiate <component.wasm> <warm-iters>
//   g2-driver copytax <component.wasm> <export-name> <iters>   (G2_LIST=<n> for list args)
//
// The engine is built ONCE, the component compiled ONCE; we time only the
// operation under test (Instance::new for instantiation; a component call for
// copy tax). Wall time via std::time::Instant; reported as µs/op.

use std::env;
use std::time::Instant;
use wasmtime::component::{Component, Linker, Instance, Val};
use wasmtime::{Config, Engine, InstanceAllocationStrategy, PoolingAllocationConfig, Store};

fn engine() -> Engine {
    let mut cfg = Config::new();
    cfg.wasm_component_model(true);
    cfg.wasm_gc(true);
    cfg.wasm_function_references(true);
    // G2_POOL=1 selects wasmtime's pooling allocator — the fast-instantiation
    // path (pre-reserved slots, reused memory mappings). This is the config a
    // spawn-primitive would actually use; default (mmap-per-instance) is the
    // conservative floor.
    if env::var("G2_POOL").ok().as_deref() == Some("1") {
        let mut pool = PoolingAllocationConfig::default();
        pool.total_component_instances(10_000);
        pool.total_core_instances(10_000);
        pool.total_memories(10_000);
        pool.total_tables(10_000);
        cfg.allocation_strategy(InstanceAllocationStrategy::Pooling(pool));
    }
    Engine::new(&cfg).expect("engine")
}

fn bench_instantiate(path: &str, warm: u64) {
    let engine = engine();
    let bytes = std::fs::read(path).expect("read component");
    let component = Component::new(&engine, &bytes).expect("compile component");
    let linker: Linker<()> = Linker::new(&engine);

    // Cold: fresh store + first instantiation, timed alone.
    let t0 = Instant::now();
    {
        let mut store = Store::new(&engine, ());
        let _inst: Instance = linker.instantiate(&mut store, &component).expect("cold inst");
    }
    let cold_ns = t0.elapsed().as_nanos();

    // Warm: reuse the same engine+component; fresh store each iteration (the
    // store is the per-instance state — this is the honest "spawn a new
    // instance" cost). Warm up first to settle allocator/icache.
    for _ in 0..50 {
        let mut store = Store::new(&engine, ());
        let _ = linker.instantiate(&mut store, &component).expect("warmup");
    }
    let t1 = Instant::now();
    for _ in 0..warm {
        let mut store = Store::new(&engine, ());
        let inst = linker.instantiate(&mut store, &component).expect("warm inst");
        std::hint::black_box(&inst);
    }
    let warm_ns = t1.elapsed().as_nanos();

    let warm_per = warm_ns as f64 / warm as f64;
    println!("instantiate\tcold_us\t{:.3}", cold_ns as f64 / 1000.0);
    println!("instantiate\twarm_us\t{:.4}\t(n={})", warm_per / 1000.0, warm);
}

fn bench_copytax(path: &str, export: &str, iters: u64) {
    let engine = engine();
    let bytes = std::fs::read(path).expect("read component");
    let component = Component::new(&engine, &bytes).expect("compile component");
    let linker: Linker<()> = Linker::new(&engine);
    let mut store = Store::new(&engine, ());
    let inst = linker.instantiate(&mut store, &component).expect("inst");

    let func = inst
        .get_func(&mut store, export)
        .unwrap_or_else(|| panic!("no export {export}"));

    let params = func.params(&store);
    let n: usize = env::var("G2_LIST").ok().and_then(|s| s.parse().ok()).unwrap_or(1000);
    let args: Vec<Val> = if params.is_empty() {
        vec![]
    } else {
        // Inspect the single param's type: a list<u32> -> build the list (this
        // path pays the canonical-ABI copy). A scalar u32 -> pass the count
        // (the baseline path, no list crossing).
        use wasmtime::component::types::Type;
        match &params[0].1 {
            Type::List(_) => {
                // list<u32> -> pays the canonical-ABI copy (scales with len)
                let list: Vec<Val> = (0..n).map(|i| Val::U32(i as u32)).collect();
                vec![Val::List(list)]
            }
            Type::Tuple(_) => {
                // tuple<u32,u32> -> flat by-value lowering (small-message proxy)
                vec![Val::Tuple(vec![Val::U32(3), Val::U32(4)])]
            }
            _ => vec![Val::U32(n as u32)],
        }
    };
    let mut results = vec![Val::U32(0)];

    for _ in 0..50 {
        func.call(&mut store, &args, &mut results).expect("warmup call");
        func.post_return(&mut store).expect("post_return");
    }
    let t = Instant::now();
    for _ in 0..iters {
        func.call(&mut store, &args, &mut results).expect("call");
        func.post_return(&mut store).expect("post_return");
    }
    let ns = t.elapsed().as_nanos();
    println!("copytax\t{}\tus_per_call\t{:.4}\t(n={})\tresult={:?}", export, ns as f64 / iters as f64 / 1000.0, iters, results[0]);
}

fn main() {
    let a: Vec<String> = env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("instantiate") => bench_instantiate(&a[2], a[3].parse().unwrap()),
        Some("copytax") => bench_copytax(&a[2], &a[3], a[4].parse().unwrap()),
        _ => {
            eprintln!("usage: g2-driver instantiate <c.wasm> <warm> | copytax <c.wasm> <export> <iters>");
            std::process::exit(2);
        }
    }
}
