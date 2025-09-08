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

    let number = heap.alloc_mature(5).unwrap();
    let bar = heap.alloc_mature("hello, world".to_owned()).unwrap();
    let baz = heap
        .alloc_mature(Baz {
            fst: 0,
            snd: true,
            thd: [1, 2, 3, 4],
        })
        .unwrap();

    let baz_deps = heap
        .alloc_mature(Baz {
            fst: 1,
            snd: false,
            thd: [2, 1, 2, 1],
        })
        .unwrap();

    let foo_struct = heap
        .alloc_mature(Foo {
            fst: 42,
            snd: "hello, world".to_owned(),
            thd: baz_deps,
        })
        .unwrap();

    println!("number: {}", *number);

    println!("number: {number:p}",);

    println!("baz.fst: {}", baz.fst);

    println!("(bas.thd[0]): {}", baz.thd[0] as usize,);

    println!("foo_struct.snd.len(): {}", foo_struct.snd.len());

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

    eprintln!("-- Young");
    heap.parse_young();
    eprintln!("-- Mature");
    heap.parse_mature();

    // eprintln!("\nMemoryManager state: {manager:?}");

    // eprintln!("\nFirst collection");
    // heap.collect(&mut manager);
    //
    // eprintln!("State after first collection");
    // eprintln!("-- Young");
    // heap.parse_young();
    //
    // eprintln!("-- Mature");
    // heap.parse_mature();
    //
    // eprintln!("\nSecond collection");
    // heap.collect(&mut manager);
    //
    // eprintln!("\nState after second collection");
    // eprintln!("-- Young");
    // heap.parse_young();
    //
    // eprintln!("-- Mature");
    // heap.parse_mature();
    //
    // eprintln!("\nMemoryManager state: {manager:?}");
    //
    // let foo_after_collect = manager.get(foo_struct_idx);
    // let bar_after_collect = manager.get(bar_idx);
    // eprintln!("Alive data pointers after moving: {bar_after_collect:p}, {baz_deps_after_collect:p}, {foo_after_collect:p}", baz_deps_after_collect = foo_after_collect.thd);
    // eprintln!("Alive data after moving: {bar_after_collect:?}, and {foo_after_collect:?}")
}
