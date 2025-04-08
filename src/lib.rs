use std::alloc::{alloc, Layout};
use std::cell::{Cell, RefCell};
use std::fmt;
use std::mem::align_of;
use std::ops::Deref;
use std::ptr::{self, NonNull};
use std::rc::Rc;

/// The garbage-collected heap.
pub struct Heap {
    /// The space for allocating new objects.
    young_space: HeapSpace,
    /// The space for evacuating objets that survived a young collection.
    mature_space: HeapSpace,
    /// The current roots that the garbage collector traces.
    roots: RefCell<Vec<NonNull<BlockHeader>>>,
}

/// A heap from- or to-space, that is a bump-allocated contiguous area.
pub struct HeapSpace {
    /// Pointer to the start of the young generation. This address is always `BlockHeader`-aligned.
    start: NonNull<u8>,
    /// Pointer to the next free address in the young generation. This address is always `BlockHeader`-aligned.
    current: Cell<NonNull<u8>>,
    /// The size of the heap space in bytes.
    size: usize,
}

/// Mask of the bit used in [BlockHeader::size] either by the mark-and-sweep garbage collector of
/// the mature space to record marked objects or by the moving collector of the young space to
/// record evacuated objects. Since we need to distinguish a forwarding pointer from the size of a
/// non-forwarded object, it must be never be set in native pointers.
///
/// In order to use the same block header implementation uniformly, and since we need the forwarded
/// bit to be set to `1` by default to mean non-forwarded (distinguishing it from pointers), we use
/// `1` to mean NON marked and `0` to mean marked, perhaps counter-intuitively. Doing so, we can
/// always initialize the mark bit to `1`.
const MARK_BIT_MASK: usize = 1;

/// A item of the collector work list.
pub struct TraceEntry {
    /// A pointer to the field of the object being traced, which is itself a pointer to a
    /// garbage-collected object. Can be null for root objects or during mark-and-sweep collection.
    field: *mut GcPtr,
    /// The pointee of the object's field.
    pointee: GcPtr,
}

impl TraceEntry {
    pub fn pointee_only(pointee: GcPtr) -> Self {
        TraceEntry {
            field: ptr::null_mut(),
            pointee,
        }
    }
}

/// A function pointer to an object implementing [Trace].
pub type Tracer = fn(*const u8, &mut Vec<TraceEntry>);

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
    /// The least significant bit holds the mark and sweep or the forwarded flag, depending on the
    /// space. So size is in the `usize-1` most significant bits of this field.
    size: usize,
    /// The padding between the header and the beginning of the object ((b) in the diagram
    /// describing [Self::size]).
    padding: usize,
    /// Pointer to the callback function that traces the object.
    tracer: Tracer,
}

impl BlockHeader {
    pub fn new(size: usize, padding: usize, tracer: Tracer) -> Self {
        Self {
            size: (size << 1) | MARK_BIT_MASK,
            padding,
            tracer,
        }
    }

    /// Marks the block as reachable.
    pub fn mark(&mut self) {
        self.size = self.size & !MARK_BIT_MASK;
    }

    /// Unmark the block after a collection.
    pub fn unmark(&mut self) {
        self.size = self.size | MARK_BIT_MASK;
    }

    /// Check if this block is marked.
    pub fn is_marked(&self) -> bool {
        (self.size & MARK_BIT_MASK) == 0
    }

    /// During a moving collection, overwrite the first word of the header (`size`) with a the new
    /// address of this object in the mature space. Since pointers are at least 2-byte aligned, the
    /// forwarding bit is zero, which distinguishes this block from an as-of-yet not moved block.
    pub fn forward(&mut self, new_ptr: GcPtr) {
        self.size = new_ptr.start.as_ptr() as usize
    }

    /// Checks if this block has been moved already during a moving collection.
    pub fn is_forwarded(&self) -> bool {
        self.is_marked()
    }

    /// Returns the forwarding address of the block if this block has already been moved during a
    /// moving collection, or `None` otherwise.
    pub fn forwarding_addr(&self) -> Option<GcPtr> {
        self.is_forwarded().then_some(GcPtr {
            start: NonNull::new(self.size as *mut BlockHeader).unwrap(),
        })
    }

    /// Returns the size of the allocated chunk in bytes (accounting for everything but the header
    /// size, see [Self::size] and [Self::full_size]), filtering out the mark bit.
    pub fn size(&self) -> usize {
        self.size >> 1
    }

    /// Returns the total size of the allocation, from the beginning of the header to the end of
    /// the value, including padding. This means that adding [Self::full_size] to `&self` points to
    /// the next block header in the heap or to the next uninitialized memory slot if this block is
    /// currently the last allocated.
    pub fn alloc_total_size(&self) -> usize {
        self.size() + std::mem::size_of::<BlockHeader>()
    }

    /// Trace and mark all reachable objects from this block.
    pub fn trace(&self) {
        let mut stack = vec![TraceEntry::pointee_only(GcPtr {
            start: NonNull::new(ptr::from_ref(self) as *mut BlockHeader).unwrap(),
        })];

        while let Some(TraceEntry {
            field: _,
            pointee: gc,
        }) = stack.pop()
        {
            eprintln!("Trace loop: popping");

            // Safety: any pointer stored in the stack must be a block header pointer in one of the
            // GC managed space. Such pointers are guaranteed to
            //
            // 1. Point to a valid block header
            // 2. The block header is followed by a valid object at the end of the header + padding
            //
            // Thus the `add` operation sill end up within the bounds of the heap space.
            let header = unsafe { &mut *(gc.start.as_ptr()) };
            let value = unsafe {
                (gc.start.as_ptr() as *const u8).add(size_of::<BlockHeader>() + header.padding)
            };

            if header.is_marked() {
                continue;
            }

            header.mark();
            (header.tracer)(value, &mut stack);
        }
    }

    /// Evacuate this block to the mature space and return the address of the new copy.
    pub fn evacuate(&mut self, to_space: &HeapSpace) -> GcPtr {
        let self_ptr: *mut BlockHeader = self;
        let new_addr = unsafe {
            to_space.copy(GcPtr {
                start: NonNull::new_unchecked(self_ptr),
            })
        };

        let mut stack = vec![TraceEntry::pointee_only(GcPtr {
            start: NonNull::new(new_addr.start.as_ptr()).unwrap(),
        })];

        while let Some(TraceEntry { pointee, field }) = stack.pop() {
            eprintln!("Evacuate loop: popping");

            let from_header = unsafe { &mut *(pointee.start.as_ptr()) };

            let new_addr = from_header.forwarding_addr().unwrap_or_else(|| unsafe {
                let to_addr = to_space.copy(pointee);
                let to_header = &*(to_addr.start.as_ptr());
                from_header.forward(to_addr);
                let to_value = (to_addr.start.as_ptr() as *const u8)
                    .add(size_of::<BlockHeader>() + to_header.padding);
                (to_header.tracer)(to_value, &mut stack);
                to_addr
            });

            unsafe {
                field.write(new_addr);
            }
        }

        new_addr
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
    fn trace(&self, _stack: &mut Vec<TraceEntry>) {}
}

impl Trace for usize {}
impl Trace for String {}
impl Trace for i32 {}

impl Heap {
    pub fn new(young_size: usize, old_size: usize) -> Self {
        Self {
            young_space: HeapSpace::new(young_size),
            mature_space: HeapSpace::new(old_size),
            roots: RefCell::new(Vec::new()),
        }
    }

    pub fn alloc_root<T: Trace>(&self, value: T) -> Gc<T> {
        let gced = self.alloc(value);
        self.root(&gced);

        gced
    }

    fn alloc<T: Trace>(&self, value: T) -> Gc<T> {
        if self.young_space.can_alloc::<T>() {
            self.young_space.alloc(value)
        } else {
            self.collect();
            self.young_space.alloc(value)
        }
    }

    pub fn root<T: Trace>(&self, managed: &Gc<T>) {
        self.roots
            .borrow_mut()
            // Safety: `header_ptr` is coming from `current`, which is NonNull
            .push(managed.start);
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

    //   pub fn sweep(&self) {
    //       let mut ptr = self.start.as_ptr();
    //       let end = self.current.get().as_ptr();
    //
    //       unsafe {
    //           while ptr < end {
    //               let header = &mut *(ptr as *mut BlockHeader);
    //               if header.is_marked() {
    //                   println!("Object {ptr:p} is marked. Keeping and unmarking");
    //                   header.unmark();
    //               } else {
    //                   println!("Object {ptr:p} is unmarked. Sweeping (in principle, currently unimplemented)");
    //               }
    //
    //               println!("Next object: {} bytes (header @ {ptr:p})", header.size());
    //               ptr = ptr.wrapping_add(header.size() + size_of::<BlockHeader>());
    //           }
    //       }
    //   }

    //   pub fn collect(&self) {
    //       self.trace();
    //       self.sweep();
    //   }

    pub fn collect(&self) {
        // For new, we never collect the old generation
        self.collect_young();
    }

    pub fn collect_young(&self) {
        for root in self.roots.borrow().iter() {
            let header = unsafe { &mut *(root.as_ptr() as *mut BlockHeader) };

            debug_assert!(
                !header.is_marked(),
                "roots should always be unmarked at the beginning of the tracing phase"
            );
            header.trace();
        }
    }
}

impl HeapSpace {
    pub fn new(size: usize) -> Self {
        unsafe {
            let start = alloc(Layout::from_size_align(size, align_of::<u8>()).unwrap());
            // We align `start` to the block header alignment for heap parsability
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
                size,
            }
        }
    }

    pub fn end(&self) -> *mut u8 {
        self.start.as_ptr().wrapping_add(self.size)
    }

    /// Checks if there is enough space to allocate a value of type `T` in this space.
    pub fn can_alloc<T: Trace>(&self) -> bool {
        let layout = Layout::new::<T>();
        let current = self.current.get().as_ptr();

        // We are overly conservative with alignement padding and use an upper bound instead of
        // computing the exact value. It doesn't matter much for a few bytes.
        current
            .wrapping_add(layout.size())
            .wrapping_add(size_of::<BlockHeader>())
            .wrapping_add(align_of::<BlockHeader>() - 1)
            .wrapping_add(layout.align() - 1)
            < self.end()
    }

    /// Checks if there is enough space to allocate a new object as a copy of an existing one.
    pub fn can_copy(&self, from: GcPtr) -> bool {
        let current = self.current.get().as_ptr();
        let header = unsafe { from.start.as_ref() };

        current.wrapping_add(header.alloc_total_size()) < self.end()
    }

    /// Allocates an object in this space, or returns `None` if the space is full.
    pub fn alloc<T: Trace>(&self, value: T) -> Gc<T> {
        let layout = Layout::new::<T>();
        let current = self.current.get().as_ptr();

        if !self.can_alloc::<T>() {
            panic!("out of memory");
            // return self.alloc(value);
        }

        unsafe {
            let prev_cur = current;
            // We need to keep one bit for the mark and seep. It's initialized to zero by default.
            assert!(layout.size() & MARK_BIT_MASK == 0);
            // Reserve space for the block header.
            // We maintain the following invariant: `current` is always `BlockHeader`-aligned
            let header_ptr = current as *mut BlockHeader;

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

    /// Copy an existing [GcPtr], potentially from a different space, to this space.
    //TODO: this is wrong! We can't guarantee that blindly copying the header and the value will
    //preserve the value's alignement. Take a value with an alignment `a` bigger than
    //`BlockHeader`'s alignement. By chance the end of the original header could end exactly at an
    //`a`-aligned address, but nothing guarantees that this is the case in the two-space.
    pub fn copy(&self, from: GcPtr) -> GcPtr {
        if !self.can_copy(from) {
            panic!("out of memory");
        }

        let current = self.current.get().as_ptr();
        let full_size = unsafe { from.start.as_ref().alloc_total_size() };

        unsafe {
            std::ptr::copy(from.start.as_ptr() as *const u8, current, full_size);
            let next_slot = current.add(full_size);
            self.current.set(NonNull::new_unchecked(next_slot));
            GcPtr {
                start: NonNull::new_unchecked(current as *mut BlockHeader),
            }
        }
    }

    fn iter(&self) -> impl std::iter::Iterator<Item = *mut BlockHeader> {
        HeapSpaceIter {
            curr: self.start.as_ptr(),
            end: self.current.get().as_ptr(),
        }
    }

    pub fn parse(&self) {
        for ptr in self.iter() {
            let header = unsafe { &*ptr };
            println!("Next object: {} bytes (header @ {ptr:p})", header.size());
        }
    }
}

struct HeapSpaceIter {
    curr: *mut u8,
    end: *mut u8,
}

impl std::iter::Iterator for HeapSpaceIter {
    type Item = *mut BlockHeader;

    fn next(&mut self) -> Option<Self::Item> {
        if self.curr >= self.end {
            return None;
        }

        let next = self.curr as *mut BlockHeader;
        let header = unsafe { &*next };
        // println!("Next object: {} bytes (header @ {ptr:p})", header.size());
        self.curr = self
            .curr
            .wrapping_add(header.size() + size_of::<BlockHeader>());

        Some(next)
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
