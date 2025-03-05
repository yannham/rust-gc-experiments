use std::alloc::{alloc, Layout};
use std::cell::{Cell, RefCell};
use std::fmt;
use std::mem::align_of;
use std::ops::Deref;
use std::ptr::{self, NonNull};

/// The garbage-collected heap.
pub struct Heap {
    /// Pointer to the start of the heap. This address is always `BlockHeader`-aligned.
    start: NonNull<u8>,
    /// Pointer to the next free address in the heap. This address is always `BlockHeader`-aligned.
    current: Cell<NonNull<u8>>,
    /// The current roots that the garbage collector traces.
    roots: RefCell<Vec<NonNull<BlockHeader>>>,
    size: usize,
}

const MARK_BIT_MASK: usize = 1 << 63;

/// The header of a heap-allocated value.
struct BlockHeader {
    /// Size in bytes of the allocated chunk, including the padding at the end of this header and
    /// before the content and the padding at the end of the content (so that the next entry is
    /// `BlockHeader`-aligned). Doesn't include the size of the header itself.
    ///
    /// That is, in the following diagram:
    ///
    /// ```text
    /// +-------------+-----------+---------+-----------+
    /// | BlockHeader | Padding   | Content | Padding   |
    /// +-------------+-----------+---------+-----------+
    /// ^             ^           ^         ^           ^
    /// |             |           |         |           |
    /// (a) start     (b) padding (c) value (d) padding (e) next
    ///
    /// `size` is `e - b` when interpreted as memory addresses.
    ///
    /// The most significant bit holds the mark and sweep flag.
    size: usize,
    /// The padding between the header and the beginning of the object ((b) in the diagram
    /// describing [Self::size]).
    padding: usize,
    /// Pointer to the callback function that traces the object.
    tracer: fn(*const u8, &mut Vec<GcPtr>),
}

impl BlockHeader {
    /// Marks the block as reachable. Returns the previous state of the mark bit (`true` if the
    /// block was already marked).
    pub fn mark(&mut self) -> bool {
        let was_marked = self.is_marked();
        self.size = self.size | MARK_BIT_MASK;
        was_marked
    }

    pub fn unmark(&mut self) {
        self.size = self.size & !MARK_BIT_MASK;
    }

    pub fn is_marked(&self) -> bool {
        self.size & MARK_BIT_MASK != 0
    }

    /// Returns the size of the allocated chunk in bytes, filtering out the mark bit.
    pub fn size(&self) -> usize {
        self.size & !MARK_BIT_MASK
    }

    pub fn trace(&self) {
        let mut stack = vec![GcPtr {
            start: NonNull::new(ptr::from_ref(self) as *mut BlockHeader).unwrap(),
        }];

        while let Some(gc) = stack.pop() {
            eprintln!("Trace loop: popping");

            let value = unsafe {
                (gc.start.as_ptr() as *const u8).add(size_of::<BlockHeader>() + self.padding)
            };
            let header = unsafe { &mut *(gc.start.as_ptr()) };

            if header.mark() {
                continue;
            }

            (header.tracer)(value, &mut stack);
        }
    }
}

pub struct Gc<T> {
    start: NonNull<BlockHeader>,
    _marker: std::marker::PhantomData<T>,
}

#[derive(Clone, Copy)]
pub struct GcPtr {
    start: NonNull<BlockHeader>,
}

impl<T> Gc<T> {
    pub fn as_gc_ptr(&self) -> GcPtr {
        GcPtr { start: self.start }
    }
}

impl<T> From<&Gc<T>> for GcPtr {
    fn from(gc: &Gc<T>) -> Self {
        gc.as_gc_ptr()
    }
}

impl<T> Clone for Gc<T> {
    fn clone(&self) -> Self {
        Self {
            start: self.start,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<T> Copy for Gc<T> {}

impl<T> Deref for Gc<T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe {
            let header = &*self.start.as_ptr();
            let value =
                (self.start.as_ptr() as *const u8).add(size_of::<BlockHeader>() + header.padding);
            &*(value as *const T)
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Gc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Gc({:?})", self.deref())
    }
}

pub trait Trace {
    fn trace(&self, _stack: &mut Vec<GcPtr>) {}
}

impl Trace for usize {}
impl Trace for String {}
impl Trace for i32 {}

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
                    "requested a heap size greater than max authorized (isize::MAX={})",
                    isize::MAX
                );
            }

            Self {
                start,
                current: Cell::new(start),
                roots: RefCell::new(Vec::new()),
                size,
            }
        }
    }

    pub fn collect(&self) {
        self.trace();
        self.sweep();
    }

    pub fn alloc_root<T: Trace>(&self, value: T) -> Gc<T> {
        self.alloc_impl(value, true)
    }

    pub fn alloc<T: Trace>(&self, value: T) -> Gc<T> {
        self.alloc_impl(value, false)
    }

    fn alloc_impl<T: Trace>(&self, value: T, root: bool) -> Gc<T> {
        let layout = Layout::new::<T>();
        let current = self.current.get().as_ptr();

        // We're out of memory. Let's try to collect.
        // We are overly conservative with alignement padding and use an upper bound instead of
        // computing the exact value. It doesn't matter much for a few bytes.
        if (current as usize)
            + layout.size()
            + size_of::<BlockHeader>()
            + (align_of::<BlockHeader>() - 1)
            + (layout.align() - 1)
            >= (self.start.as_ptr() as usize) + self.size
        {
            self.collect();
            return self.alloc_impl(value, root);
        }

        unsafe {
            let prev_cur = current;
            // We need to keep one bit for the mark and seep. It's initialized to zero by default.
            assert!(layout.size() & MARK_BIT_MASK == 0);
            // Reserve space for the block header.
            // We maintain the following invariant: `current` is always `BlockHeader`-aligned
            let header_ptr = current as *mut BlockHeader;

            if root {
                self.roots
                    .borrow_mut()
                    // Safety: `header_ptr` is coming from `current`, which is NonNull
                    .push(NonNull::new_unchecked(header_ptr));
            }

            // Advance the current pointer to the next free address.

            // Safety:
            // 1. size_of::<BlockHeader>() is 8 currently and will never exceed a few words, so it
            //    won't overflow isize
            // 2. The check at the beginning of this function ensures that we are still in the
            //    boundaries of the same initial heap allocation.
            let unaligned_slot = current.add(size_of::<BlockHeader>());

            // Safety:
            // 1. layout.align() * sizeof::<u8>() doesn't overflow isize: we check this explicitly
            // 2. current is derived from the initial allocation in Heap::new(), and the check at
            //    the beginning of this function precisely ensures that when offset by
            //    `layout.size() + size_of::<BlockHeader>()` plus potential padding, this remains
            //    in the original range of allocated memory.
            assert!(layout.align() * size_of::<u8>() < (isize::MAX as usize));
            let slot = align_up(unaligned_slot, layout.align());

            // Safety: see the justification for the call to `align_up` above.
            // We maintain the  invariant that the next current pointer is `BlockHeader`-aligned.
            let next_slot = align_up(slot.add(layout.size()), align_of::<BlockHeader>());
            // Safety: `next_slot` is an offset from the `self.current`, which is non null
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
                    padding: (slot as usize) - (unaligned_slot as usize),
                    tracer: |obj, stack| T::trace(&*(obj as *const T), stack),
                },
            );

            // Finally write `value` to the newly reserved slot

            let slot = slot as *mut T;
            // Safety: current is valid for write (alloced, unitialized memory) and is properly
            // aligned thanks to the call to `align_up`.
            ptr::write(slot, value);

            Gc {
                start: NonNull::new_unchecked(header_ptr),
                _marker: std::marker::PhantomData,
            }
        }
    }

    pub fn parse(&self) {
        let mut ptr = self.start.as_ptr();
        let end = self.current.get().as_ptr();

        unsafe {
            while ptr < end {
                let header = &*(ptr as *mut BlockHeader);
                println!("Next object: {} bytes (header @ {ptr:p})", header.size());
                ptr = ptr.wrapping_add(header.size() + size_of::<BlockHeader>());
            }
        }
    }

    fn trace(&self) {
        for root in self.roots.borrow().iter() {
            eprintln!("Tracing root {root:p}");

            let header = unsafe { &mut *(root.as_ptr() as *mut BlockHeader) };
            debug_assert!(
                !header.is_marked(),
                "roots should always be unmarked at the beginning of the tracing phase"
            );
            header.trace();
        }
    }

    pub fn sweep(&self) {
        let mut ptr = self.start.as_ptr();
        let end = self.current.get().as_ptr();

        unsafe {
            while ptr < end {
                let header = &mut *(ptr as *mut BlockHeader);
                if header.is_marked() {
                    println!("Object {ptr:p} is marked. Keeping and unmarking");
                    header.unmark();
                } else {
                    println!("Object {ptr:p} is unmarked. Sweeping (in principle, currently unimplemented)");
                }

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
    // 3. Offset the ptr by this value
    let offset = ((!(ptr as usize) & (align - 1)) + 1) & (align - 1);
    ptr.add(offset)
}

/// Unsafety: the preconditions to avoid Undefined Behavior are the same as for `std::ptr::add`.
/// This methods keeps the address provenance information.
///
/// Requires that `align` is a power of 2.
unsafe fn align_down(ptr: *mut u8, align: usize) -> *mut u8 {
    let offset = (ptr as usize) & (align - 1);
    ptr.sub(offset)
}
