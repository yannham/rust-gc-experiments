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

    println!(
        "Some operation involving alloced objects {}",
        baz.fst
            + *number
            + (baz.thd[0] as usize)
            + foo_struct.snd.len()
            + (baz_deps.thd[2] as usize)
    );

    println!("Alloced {number:?}, {bar:?}, {baz:?}, {baz_deps:?} and {foo_struct:?}");

    eprintln!("-- Young");
    heap.parse_young();
    eprintln!("-- Mature");
    heap.parse_mature();
}
