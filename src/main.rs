use nicki_menaj::{Gc, GcPtr, Heap, MemoryManager, Trace, TraceEntry};

#[derive(Debug)]
struct Baz {
    fst: usize,
    snd: bool,
    thd: [u32; 4],
}

#[derive(Debug)]
struct Foo {
    fst: usize,
    snd: String,
    thd: Gc<Baz>,
}

impl Trace for Baz {
    fn trace(&mut self, _stack: &mut Vec<TraceEntry>) {
        eprintln!("Tracing baz");
    }
}

impl Trace for Foo {
    fn trace(&mut self, stack: &mut Vec<TraceEntry>) {
        eprintln!("Tracing foo");
        stack.push(self.thd.as_trace_entry());
    }
}

fn main() {
    let heap = Heap::new(12 * 1024 * 1024, 64 * 1024 * 1024);
    let mut manager = MemoryManager::new();

    let number_idx = manager.root(&heap, 5);
    let number = manager.get(number_idx);

    let bar_idx = manager.root(&heap, "hello, world".to_owned());
    let bar = manager.get(bar_idx);

    let baz_idx = manager.root(
        &heap,
        Baz {
            fst: 0,
            snd: true,
            thd: [1, 2, 3, 4],
        },
    );
    let baz = manager.get(baz_idx);

    let baz_deps_idx = manager.root(
        &heap,
        Baz {
            fst: 1,
            snd: false,
            thd: [2, 1, 2, 1],
        },
    );
    let baz_deps = manager.get(baz_deps_idx);

    let foo_struct_idx = manager.root(
        &heap,
        Foo {
            fst: 42,
            snd: "hello, world".to_owned(),
            thd: baz_deps,
        },
    );
    let foo_struct = manager.get(foo_struct_idx);

    println!(
        "Some operation {}",
        baz.fst
            + *number
            + (baz.thd[0] as usize)
            + foo_struct.snd.len()
            + (baz_deps.thd[2] as usize)
    );

    println!("Alloced {number:?}, {bar:?}, {baz:?}, {baz_deps:?} and {foo_struct:?}");
    println!("Unrooting everything but \"hello world\" and Foo struct");

    manager.unroot(number_idx);
    manager.unroot(baz_idx);
    manager.unroot(baz_deps_idx);

    // We must make sure to not re-use the non-indexed pointers after here, as they might be
    // overwritten!

    eprintln!("State before first collection");
    eprintln!("-- Young");
    heap.parse_young();
    eprintln!("-- Mature");
    heap.parse_mature();

    eprintln!("\nMemoryManager state: {manager:?}");

    eprintln!("\nFirst collection");
    heap.collect(&mut manager);

    eprintln!("State after first collection");
    eprintln!("-- Young");
    heap.parse_young();

    eprintln!("-- Mature");
    heap.parse_mature();

    eprintln!("\nSecond collection");
    heap.collect(&mut manager);

    eprintln!("\nState after second collection");
    eprintln!("-- Young");
    heap.parse_young();

    eprintln!("-- Mature");
    heap.parse_mature();

    eprintln!("\nMemoryManager state: {manager:?}");

    let foo_after_collect = manager.get(foo_struct_idx);
    let bar_after_collect = manager.get(bar_idx);
    eprintln!("Alive data pointers after moving: {bar_after_collect:p}, {baz_deps_after_collect:p}, {foo_after_collect:p}", baz_deps_after_collect = foo_after_collect.thd);
    eprintln!("Alive data after moving: {bar_after_collect:?}, and {foo_after_collect:?}")
}
