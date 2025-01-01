mod lib;

use bump_alloc::Heap;

#[derive(Debug)]
struct Baz {
    fst: usize,
    snd: bool,
    thd: [u32; 4],
}

fn main() {
    let heap = Heap::new(64*1024*1024);

    let foo = heap.alloc(5);
    let bar = heap.alloc("hello, world".to_owned());
    let baz = heap.alloc(Baz {
        fst: 0,
        snd: true,
        thd: [1,2,3,4],
    });

    println!("Alloced {foo}, {bar} and {baz:?}");

    heap.parse();
}
