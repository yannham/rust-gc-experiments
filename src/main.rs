use bump_alloc::{Gc, GcPtr, Heap, Trace};

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
    fn trace(&self, _stack: &mut Vec<GcPtr>) {
        eprintln!("Tracing baz");
    }
}

impl Trace for Foo {
    fn trace(&self, stack: &mut Vec<GcPtr>) {
        eprintln!("Tracing foo");
        stack.push(self.thd.as_gc_ptr());
    }
}

fn main() {
    let heap = Heap::new(12 * 1024 * 1024, 64 * 1024 * 1024);

    let foo = heap.alloc(5);
    let bar = heap.alloc_root("hello, world".to_owned());
    let baz = heap.alloc(Baz {
        fst: 0,
        snd: true,
        thd: [1, 2, 3, 4],
    });

    let baz_deps = heap.alloc(Baz {
        fst: 1,
        snd: false,
        thd: [2, 1, 2, 1],
    });

    let foo_struct = heap.alloc_root(Foo {
        fst: 42,
        snd: "hello, world".to_owned(),
        thd: baz_deps,
    });

    println!(
        "Some operation {}",
        baz.fst + *foo + (baz.thd[0] as usize) + foo_struct.snd.len() + (baz_deps.thd[2] as usize)
    );

    println!("Alloced {foo:?}, {bar:?}, {baz:?}, {baz_deps:?} and {foo_struct:?}");

    eprintln!("First collection");
    heap.collect();
    eprintln!("Second collection");
    heap.collect();
}
