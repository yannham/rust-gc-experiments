mod lib;

use bump_alloc::{Heap, Trace};

#[derive(Debug)]
struct Baz {
    fst: usize,
    snd: bool,
    thd: [u32; 4],
}

impl Trace for Baz {
    fn trace(&self) {
        println!("Tracing baz");
    }
}

fn main() {
    let heap = Heap::new(64 * 1024 * 1024);

    let foo = heap.alloc(5);
    let bar = heap.alloc_root("hello, world".to_owned());
    let baz = heap.alloc_root(Baz {
        fst: 0,
        snd: true,
        thd: [1, 2, 3, 4],
    });

    println!("Alloced {foo}, {bar} and {baz:?}");

    heap.collect();
    heap.collect();
}
