use std::alloc::{alloc, Layout};
use std::cell::Cell;
use std::mem::align_of;
use std::ptr::{self, NonNull};

pub struct Heap {
    start: NonNull<u8>,
    current: Cell<NonNull<u8>>,
    size: usize,
}

pub struct BlockHeader {
    // Size in bytes of the allocated chunk. The most significant bit holds the mark and sweep
    // flag.
    size: usize,
}

trait Trace {}

impl Heap {
    pub fn new(size: usize) -> Self {
        unsafe {
            let start = alloc(Layout::from_size_align(size, align_of::<u8>()).unwrap());
            // We align `start` to the block header alignement for heap parsability
            let start = align_up(start, align_of::<BlockHeader>());

            let Some(start) = NonNull::new(start) else {
                panic!("out of memory");
            };

            if size >= (isize::MAX as usize) {
                panic!(
                    "requested a heap size greater than max authorized (isize::MAX={}",
                    isize::MAX
                );
            }

            Self {
                start,
                current: Cell::new(start),
                size,
            }
        }
    }

    pub fn collect(&self) {
        panic!("out of heap memory (collect is unimplemented)");
    }

    pub fn alloc<T>(&self, value: T) -> &mut T {
        let layout = Layout::new::<T>();
        let current = self.current.get().as_ptr();

        // We're out of memory. Let's try to collect.
        // We are overly conservative with alignement, and use an upper bound instead of computing
        // the exact value. It doesn't matter much for a few bytes.
        if (current as usize)
            + layout.size()
            + size_of::<BlockHeader>()
            + (align_of::<BlockHeader>() - 1)
            + (layout.align() - 1)
            >= (self.start.as_ptr() as usize) + self.size
        {
            self.collect();
            return self.alloc(value);
        }

        unsafe {
            let prev_cur = current;
            // We need to keep one bit for the mark and seep. It's initialized to zero by default.
            assert!(layout.size() < (1 << 63));
            // Reserve space for the block header.
            // We use the following invariant of the heap: `current` is always
            // `BlockHeader`-aligned
            let header_ptr = current as *mut BlockHeader;

            // Advance the current pointer to the next free address.

            // Safety:
            // 1. size_of::<BlockHeader>() is 8 currently and will never exceed a few words, so it
            //    won't overflow isize
            // 2. The check at the beginning of this function ensures that we are still in boundary
            //    of the same initial heap allocation.
            let unaligned_slot = current.add(size_of::<BlockHeader>());

            // Safety:
            // 1. layout.align() * sizeof::<u8>() doesn't overflow isize: we check this explicitly
            // 2. current is derived from the initial allocation in Heap::new(), and the check at
            //    the beginning of this function precisely ensures that when offset by
            //    `layout.size() + size_of::<BlockHeader>()`, this remains in the original range of
            //    allocated memory.
            assert!(layout.align() * size_of::<u8>() < (isize::MAX as usize));
            let slot = align_up(unaligned_slot, layout.align());

            // Safety: see the justification for the call to `align_up` above.
            // We maintain the  invariant that the next current pointer is `BlockHeader`-aligned.
            let next_slot = align_up(slot.add(layout.size()), align_of::<BlockHeader>());
            self.current.set(NonNull::new_unchecked(next_slot));

            // Now that we have the total size of the allocated chunk including padding, we can
            // write the block header.
            println!(
                "Writing block header (size {}) to {header_ptr:p} (current was {prev_cur:p})",
                (next_slot as usize) - (unaligned_slot as usize)
            );
            ptr::write(
                header_ptr,
                BlockHeader {
                    size: (next_slot as usize) - (unaligned_slot as usize),
                },
            );

            // Finally write `value` to the newly reserved slot

            let slot = slot as *mut T;
            // Safety: current is valid for write (alloced, unitialized memory) and is properly
            // aligned thanks to the call to `align_up`.
            ptr::write(slot, value);

            &mut *slot
        }
    }

    pub fn parse(&self) {
        let mut ptr = self.start.as_ptr();
        let end = self.current.get().as_ptr();

        unsafe {
            while ptr < end {
                let header = &*(ptr as *mut BlockHeader);
                println!("Next object: {} bytes (header @ {ptr:p})", header.size);
                ptr = ptr.wrapping_add(header.size + size_of::<BlockHeader>());
            }
        }
    }
}

/// Unsafety: the preconditions to avoid Undefined Behavior are the same as for `std::ptr::add`.
/// This methods keeps the address provenance information.
///
/// Requires that `align` is a power of 2.
unsafe fn align_up(ptr: *mut u8, align: usize) -> *mut u8 {
    // 1. Extract the complement to `align` (same as 2 complement) of `remainder = ptr % align`.
    //    That is `!remainder + 1` which is `align - remainder` if `remainder != 0`, or `align`
    //    otherwise.
    // 2. Take the modulo `align` again to get exactly `align - remainder`
    // 3. Offset he ptr by this value
    let offset = ((!(ptr as usize) & (align - 1)) + 1) & (align - 1);
    ptr.add(offset)
}
