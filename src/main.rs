mod lib;

use bump_alloc::{Gc, Heap, Trace};

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
    fn trace(&self) {
        println!("Tracing baz");
    }
}

impl Trace for Foo {
    fn trace(&self) {
        println!("Tracing foo");
        self.thd.trace();
    }
}

fn main() {
    let heap = Heap::new(64 * 1024 * 1024);

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

    println!("Some operation {}", baz.fst + *foo + (baz.thd[0] as usize));

    println!("Alloced {foo:?}, {bar:?}, {baz:?}, {baz_deps:?} and {foo_struct:?}");

    heap.collect();
    heap.collect();
}
