use std::alloc::{Layout, alloc};
use std::cell::{Cell, RefCell};
use std::fmt;
use std::marker::PhantomData;
use std::mem::align_of;
use std::ops::Deref;
use std::ptr::{self, NonNull};
use std::cmp::max;

#[cfg(test)]
mod tests;
mod alloc;

use alloc::AllocState;

/// The garbage-collected heap.
pub struct Heap {
    /// The space for allocating new objects.
    pub(crate) young_space: YoungSpace,
    /// The space for evacuating objets that survived a young collection.
    pub(crate) mature_space: MatureSpace,
}

/// Contiguous allocated region of memory in the heap.
pub struct HeapSpace {
    /// Pointer to the start of the young generation. This address is always `BlockHeader`-aligned.
    start: NonNull<u8>,
    /// The size of the heap space in bytes.
    size: usize,
}

/// A item of the collector work list.
#[derive(Clone, Copy)]
pub struct TraceEntry {
    /// A pointer to the field of the object being traced, which is itself a pointer to a
    /// garbage-collected object.
    pub field: *mut NonNull<BlockHeader>,
}

pub trait AllocSpace {
    /// Copy the content of an existing [GcPtr], potentially from a different space, to this space.
    /// This creates a new distinct [GcPtr].
    fn copy(&self, obj: GcPtr) -> GcPtr;

    /// Checks if a pointer is contained in this space.
    fn contains(&self, ptr: *const BlockHeader) -> bool;
}

impl TraceEntry {
    /// Trace and mark all reachable objects from this block.
    ///
    /// # Safety
    ///
    /// `self.field` must be a valid, writable pointer to a [GcPtr].
    pub unsafe fn mark(self) {
        let mut stack = vec![self];
        while let Some(TraceEntry { field }) = stack.pop() {
            eprintln!("Trace loop: popping");

            // Safety: any pointer stored in the stack must be a block header pointer in one of the
            // GC managed space. Such pointers are guaranteed to
            //
            // 1. Point to a valid block header
            // 2. The block header is followed by a valid object at the end of the header + padding
            //
            // Thus the `add` operation sill end up within the bounds of the heap space.
            let start = unsafe { (*field).as_ptr() };
            let header = unsafe { &mut *start };
            // unwrap(): we assume that we don't call `mark` on empty blocks
            let value = unsafe { BlockHeader::data_ptr(*field).unwrap() };

            if header.is_marked() {
                continue;
            }

            header.mark();
            (header.tracer)(value.as_ptr(), &mut stack);
        }
    }

    /// Evacuate the block pointed to by the field of this trace entry to the mature space and
    /// update the trace entry with the address of the new copy.
    ///
    /// # Safety
    ///
    /// `self.field` must be a valid, writable pointer to a [GcPtr].
    pub fn evacuate(self, to_space: &impl AllocSpace) {
        let mut stack = vec![self];

        while let Some(TraceEntry { field }) = stack.pop() {
            let pointee = unsafe { *field };

            if to_space.contains(pointee.as_ptr()) {
                eprintln!("Entry {pointee:p} is already in the target space, skipping");
                continue;
            }

            eprintln!("Evacuate loop: processing {field:p} -> {pointee:p}");

            let forwarding_addr = unsafe {
                let from_header = &mut (*pointee.as_ptr());
                from_header.forwarding_addr()
            };

            if let Some(forwarding_addr) = forwarding_addr {
                eprintln!("Found forwarding address {forwarding_addr:p}");
            }

            let new_addr = forwarding_addr.unwrap_or_else(|| unsafe {
                let to_addr = to_space.copy(GcPtr { start: pointee });
                {
                    let from_header = &mut (*pointee.as_ptr());
                    from_header.forward(to_addr);
                }
                let to_value = to_addr.data_ptr();
                {
                    let to_header = &*(to_addr.start.as_ptr());
                    (to_header.tracer)(to_value.as_ptr(), &mut stack);
                }
                to_addr
            });

            eprintln!("Moved {:p} to {:p}", pointee, new_addr.start);

            unsafe {
                field.write(new_addr.start);
            }
        }
    }
}

/// A function pointer to an object implementing [Trace].
pub type Tracer = fn(*mut u8, &mut Vec<TraceEntry>);

/// A tracer that does nothing.
fn noop_tracer(_: *mut u8, _: &mut Vec<TraceEntry>) {}

/// The two type of blocks (free or allocated). For free blocks, we include there the additional
/// data of the next free block in the list, if any.
#[derive(Debug)]
pub enum BlockType {
    Allocated,
    Free { next: Option<NonNull<BlockHeader>> },
}

/// The header of a heap-allocated value.
#[derive(Debug)]
pub struct BlockHeader {
    /// The mark and sweep or the forwarded flag, depending on the space.
    mark_bit: bool,
    /// If this block is allocated or not (and associated metadata).
    block_type: BlockType,
    /// The log2 of the alignment of the object. We need this information when moving objects from
    /// a from-space to a to-space: while the slots of a space are always `BlockHeader`-aligned,
    /// it's not guaranteed that copying blindly the bytes will result in a aligned pointer for the
    /// beginning of the content. Upon moving, we thus recompute padding, which requires to know
    /// the alignment. We only need 6 bits to represent any power of 2 representable on 64 bits.
    align: u8,
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
    /// `size` is `e - b` when interpreted as memory addresses. This allow to jump to the next
    /// object in the heap without recomputing the size from the various paddings.
    ///
    /// This is the same for free blocks, considering that there's no padding.
    //TODO: should we have size = e - a instead?
    size: usize,
    /// The padding between the header and the beginning of the object (`c - b` in the diagram
    /// describing [Self::size]).
    start_padding: u8,
    /// The padding between the end of the object and the next header (`e - d` in the diagram)
    end_padding: u8,
    /// Pointer to the callback function that traces the object.
    tracer: Tracer,
}

impl BlockHeader {
    /// Create a new block header, given the size of the object, its alignment, its padding and the
    /// tracer. The alignment is given in bytes, and must be a power of 2.
    pub fn new(
        size: usize,
        align: usize,
        start_padding: usize,
        end_padding: usize,
        tracer: Tracer,
    ) -> Self {
        let align_log2 = align.ilog2();

        assert!(align_log2 <= u8::MAX as u32);
        assert!(start_padding <= u8::MAX as usize);
        assert!(end_padding <= u8::MAX as usize);

        Self {
            mark_bit: false,
            block_type: BlockType::Allocated,
            align: align_log2 as u8,
            size,
            start_padding: start_padding as u8,
            end_padding: end_padding as u8,
            tracer,
        }
    }

    /// Creates a new header for an empty block with the given size.
    pub fn empty(size: usize, next: Option<NonNull<BlockHeader>>) -> Self {
        Self {
            mark_bit: false,
            block_type: BlockType::Free { next },
            align: 0,
            size,
            start_padding: 0,
            end_padding: 0,
            tracer: noop_tracer,
        }
    }

    /// Marks the block as reachable.
    pub fn mark(&mut self) {
        self.mark_bit = true;
    }

    /// Unmark the block after a collection.
    pub fn unmark(&mut self) {
        self.mark_bit = false;
    }

    /// Check if this block is marked.
    pub fn is_marked(&self) -> bool {
        eprintln!("Size (or pointer, if forwarded): {} bytes", self.size);
        self.mark_bit
    }

    // Old doc
    // During a moving collection, overwrite the first word of the header (`size`) with a the new
    // address of this object in the mature space. Since pointers are at least 2-byte aligned, the
    // forwarding bit is zero, which distinguishes this block from an as-of-yet not moved block.

    /// Overwrite the `size` data with a forwarding address, and set the mark bit to `true`/`1`, to
    /// indicate that this block has been moved already.
    pub fn forward(&mut self, new_ptr: GcPtr) {
        self.size = new_ptr.start.as_ptr() as usize;
        self.mark_bit = true;
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

    /// Returns the the alignment in bytes of the content.
    pub fn align(&self) -> usize {
        1 << self.align
    }

    /// Returns the total size of the allocation, from the beginning of the header to the end of
    /// the value, including padding. This means that adding [Self::full_size] to `&self` points to
    /// the next block header in the heap or to the next uninitialized memory slot if this block is
    /// currently the last allocated.
    pub fn alloc_total_size(&self) -> usize {
        self.size + std::mem::size_of::<BlockHeader>()
    }

    /// Given a free block, checks that the block is big enough to store a value with the provided
    /// layout, including potential padding.
    pub fn can_store(&self, layout: Layout) -> bool {
        assert!(matches!(self.block_type, BlockType::Free { .. }));

        unsafe {
            let self_ptr = self as *const BlockHeader;
            let slot = align_up_cst(self_ptr.wrapping_add(1).cast(), layout.align());
            assert!(layout.align() * size_of::<u8>() < (isize::MAX as usize));
            let next_slot =
                align_up_cst(slot.wrapping_add(layout.size()), align_of::<BlockHeader>());

            (next_slot as usize) <= (self_ptr as usize) + size_of::<BlockHeader>() + self.size
        }
    }

    /// Returns the pointer to the beginning of the data stored in this block.
    pub fn data_ptr(this: NonNull<BlockHeader>) -> Option<NonNull<u8>> {
        unsafe {
            let block_ref = this.as_ref();

            if matches!(block_ref.block_type, BlockType::Free { .. }) {
                return None;
            }

            let padding = block_ref.start_padding;

            let this_u8: NonNull<u8> = this.cast();
            Some(this_u8.add(size_of::<BlockHeader>() + (padding as usize)))
        }
    }

    /// Returns the layout of the object stored in this block. If the block is empty, returns
    /// `None`.
    pub fn layout(&self) -> Option<Layout> {
        if let BlockType::Free { .. } = self.block_type {
            return None;
        }

        let size = self.size - (self.start_padding as usize) - (self.end_padding as usize);
        Some(Layout::from_size_align(size, self.align()).unwrap())
    }
}

pub struct Gc<T> {
    start: NonNull<BlockHeader>,
    _marker: PhantomData<T>,
}

#[derive(Clone, Copy)]
pub struct GcPtr {
    start: NonNull<BlockHeader>,
}

impl GcPtr {
    pub fn data_ptr(&self) -> NonNull<u8> {
        BlockHeader::data_ptr(self.start).unwrap()
    }
}

impl std::fmt::Debug for GcPtr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "GcPtr({:p})", self.start)
    }
}

impl<T> Gc<T> {
    pub fn as_gc_ptr(&self) -> GcPtr {
        GcPtr { start: self.start }
    }

    pub fn data_ptr(&self) -> NonNull<u8> {
        self.as_gc_ptr().data_ptr()
    }

    pub fn as_trace_entry(&mut self) -> TraceEntry {
        TraceEntry {
            field: &mut self.start as *mut NonNull<BlockHeader>,
        }
    }

    /// Casts an  "untyped" [GcPtr] to [Self].
    ///
    /// # Safety
    ///
    /// The type of the object actually stored in the GC allocation must be `T`.
    pub unsafe fn from_gc_ptr(gc_ptr: GcPtr) -> Self {
        Gc {
            start: gc_ptr.start,
            _marker: PhantomData,
        }
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
            _marker: PhantomData,
        }
    }
}

impl<T> Copy for Gc<T> {}

impl<T> Deref for Gc<T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe {
            let value = self.data_ptr().as_ptr();
            &*(value as *const T)
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Gc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Gc({:?})", self.deref())
    }
}

// impl fmt::Debug for BlockHeader {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         write!(
//             f,
//             "BlockHeader {{ size: {}, align: {}, start_padding: {}, end_padding: {}, marked: {}, type: {} }}",
//             self.size,
//             self.align(),
//             self.start_padding,
//             self.end_padding,
//             self.mark_bit,
//             match &self.block_type {
//                 BlockType::Allocated => "Allocated".to_string(),
//                 BlockType::Free { next } => format!(
//                     "Free {{ next: {} }}",
//                     next.map_or("None".to_string(), |n| format!("{:p}", n))
//                 ),
//             }
//         )
//     }
// }

pub trait Trace: Sized {
    fn trace(&mut self, _stack: &mut Vec<TraceEntry>) {}

    // If needed, we could move the `Sized` bound here, it at some point we have a DST and we want
    // to implement only `trace_untyped` directly.
    fn trace_untyped(this: *mut u8, stack: &mut Vec<TraceEntry>) {
        unsafe {
            let this = &mut *(this as *mut Self);
            this.trace(stack);
        }
    }
}

impl Trace for usize {}
impl Trace for String {}
impl Trace for i32 {}

impl Heap {
    pub fn new(young_size: usize, old_size: usize) -> Self {
        Self {
            young_space: YoungSpace::new(young_size),
            mature_space: MatureSpace::new(old_size),
        }
    }

    /// Returns `true` if there is sufficient room in the young space to allocate an object of type
    /// `T`.
    pub fn can_alloc_young<T: Trace>(&self) -> bool {
        self.young_space.can_alloc::<T>()
    }

    pub fn alloc_young<T: Trace>(&self, value: T) -> Option<Gc<T>> {
        self.young_space
            .can_alloc::<T>()
            .then(|| self.young_space.alloc(value))
    }

    pub fn alloc_mature<T: Trace>(&self, value: T) -> Option<Gc<T>> {
        Some(self.mature_space.alloc(value))
    }

    pub fn collect_mature(&self, stack: &mut MemoryManager) {
        self.mature_space.collect(stack);
    }

    pub fn collect_young(&self, stack: &mut MemoryManager) {
        for entry in stack.iter_mut_as_trace_entries() {
            let root = unsafe { *entry.field };
            eprintln!("-- Processing root {root:p}");

            if !self.young_space.space.contains(root.as_ptr()) {
                eprintln!("Root {root:p} is not in the young space, skipping");
                continue;
            }

            debug_assert!(
                unsafe {
                    !(root.as_ptr() as *const BlockHeader)
                        .as_ref()
                        .unwrap()
                        .is_marked()
                },
                "roots should always be unmarked at the beginning of the tracing phase"
            );

            entry.evacuate(&self.mature_space);
            eprintln!(
                "Moved root {root:p} -> {dst:p}",
                dst = unsafe { *entry.field }
            );
        }

        //TODO: should be a reset() method or smth
        self.young_space.current.set(self.young_space.space.start);
    }

    pub fn parse_young(&self) {
        self.young_space.parse();
    }

    pub fn parse_mature(&self) {
        self.mature_space.parse();
    }
}

pub struct YoungSpace {
    space: HeapSpace,
    /// Pointer to the next free address. This address is always `BlockHeader`-aligned.
    current: Cell<NonNull<u8>>,
}

pub struct MatureSpace {
    space: RefCell<AllocState>,
}

impl HeapSpace {
    pub fn new(size: usize) -> Self {
        unsafe {
            assert!(
                size >= size_of::<BlockHeader>(),
                "heap size too small: a heap must be able to fit at least one block header"
            );
            let start = alloc(Layout::from_size_align(size, align_of::<BlockHeader>()).unwrap());

            let Some(start) = NonNull::new(start) else {
                panic!("out of memory")
            };

            if size >= (isize::MAX as usize) {
                panic!(
                    "requested a heap size greater than max authorized (isize::MAX={})",
                    isize::MAX
                );
            }

            Self { start, size }
        }
    }

    pub fn end(&self) -> *mut u8 {
        // Safety: the end pointer is considered to be part of the allocation as per my current
        // understanding of the semantics of pointer provenance in Rust.
        unsafe { self.start.as_ptr().add(self.size) }
    }

    pub fn contains(&self, ptr: *const BlockHeader) -> bool {
        let ptr = ptr as *const u8;
        let start = self.start.as_ptr();

        ptr >= start && ptr < self.end()
    }
}

impl YoungSpace {
    /// Creates a new young space with the given size.
    pub fn new(size: usize) -> Self {
        let space = HeapSpace::new(size);

        YoungSpace {
            current: Cell::new(space.start),
            space,
        }
    }

    /// Checks if there is enough space to allocate a value of type `T` in this space. Same as
    /// `self.0.can_alloc_layout(Layout::new::<T>())`.
    pub fn can_alloc<T: Trace>(&self) -> bool {
        self.can_alloc_layout(Layout::new::<T>())
    }

    /// Checks if there is enough space to allocate a new object with a given layout in this space.
    pub fn can_alloc_layout(&self, layout: Layout) -> bool {
        let current = self.current.get().as_ptr();

        // We are overly conservative with alignment padding and use an upper bound instead of
        // computing the exact value. It doesn't matter much for a few bytes.
        current
            .wrapping_add(layout.size())
            .wrapping_add(size_of::<BlockHeader>())
            .wrapping_add(align_of::<BlockHeader>() - 1)
            .wrapping_add(layout.align() - 1)
            < self.space.end()
    }

    // /// Checks if there is enough space to allocate a new object as a copy of an existing one.
    // pub fn can_copy(&self, from: GcPtr) -> bool {
    //     let current = self.0.current.get().as_ptr();
    //     let header = unsafe { from.start.as_ref() };
    //
    //     current.wrapping_add(header.alloc_total_size()) < self.0.end()
    // }

    /// Allocates an object in this space, or returns `None` if the space is full.
    pub fn alloc<T: Trace>(&self, value: T) -> Gc<T> {
        let layout = Layout::new::<T>();
        let current = self.current.get().as_ptr();

        if !self.can_alloc::<T>() {
            panic!("out of memory");
            // return self.0.alloc(value);
        }

        unsafe {
            let prev_cur = current;
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
            // Safety: `next_slot` is an offset from the `self.0.current`, which is non null
            self.current.set(NonNull::new_unchecked(next_slot));

            // Now that we have the total size of the allocated chunk including padding, we can
            // write the block header.
            println!(
                "Writing block header (size {}) to {header_ptr:p} (current was {prev_cur:p})",
                (next_slot as usize) - (unaligned_slot as usize)
            );
            ptr::write(
                header_ptr,
                BlockHeader::new(
                    (next_slot as usize) - (unaligned_slot as usize),
                    layout.align(),
                    (slot as usize) - (unaligned_slot as usize),
                    (next_slot as usize) - (slot as usize + layout.size()),
                    |obj, stack| T::trace(&mut *(obj as *mut T), stack),
                ),
            );

            // Finally write `value` to the newly reserved slot

            let slot = slot as *mut T;
            // Safety: current is valid for write (alloced, unitialized memory) and is properly
            // aligned thanks to the call to `align_up`.
            ptr::write(slot, value);

            Gc {
                start: NonNull::new_unchecked(header_ptr),
                _marker: PhantomData,
            }
        }
    }

    fn iter(&self) -> impl std::iter::Iterator<Item = *mut BlockHeader> {
        HeapSpaceIter {
            curr: self.space.start.as_ptr(),
            end: self.current.get().as_ptr(),
        }
    }

    pub fn parse(&self) {
        for ptr in self.iter() {
            let header = unsafe { &*ptr };
            println!(
                "Next object: {} bytes (header @ {ptr:p}), type: {:?}",
                header.size, header.block_type
            );
        }
    }
}

impl AllocSpace for YoungSpace {
    fn copy(&self, from: GcPtr) -> GcPtr {
        let from_header = unsafe { from.start.as_ref() };

        let layout = {
            let header = unsafe { from.start.as_ref() };
            Layout::from_size_align(header.size, header.align()).unwrap()
        };

        if !self.can_alloc_layout(layout) {
            panic!("out of memory");
        }

        let current = self.current.get().as_ptr();

        // See Self::alloc for safety and explanation. The following is just a simpler version of
        // allocation, where we copy chunks of the original object instead of writing new data.
        unsafe {
            let header_ptr = current as *mut BlockHeader;

            let unaligned_slot = current.add(size_of::<BlockHeader>());

            assert!(layout.align() * size_of::<u8>() < (isize::MAX as usize));
            let slot = align_up(unaligned_slot, layout.align());

            let next_slot = align_up(slot.add(layout.size()), align_of::<BlockHeader>());
            self.current.set(NonNull::new_unchecked(next_slot));

            // Now that we have the total size of the allocated chunk including padding, we can
            // write the block header.
            println!(
                "Copying block header (size {}) from_header {from_header:p} -> {header_ptr:p}",
                (next_slot as usize) - (unaligned_slot as usize)
            );

            ptr::write(
                header_ptr,
                BlockHeader::new(
                    (next_slot as usize) - (unaligned_slot as usize),
                    layout.align(),
                    (slot as usize) - (unaligned_slot as usize),
                    (next_slot as usize) - (slot as usize + layout.size()),
                    from_header.tracer,
                ),
            );

            let from_content_start = from.data_ptr();
            // The size of the content only
            let content_size = from_header.size
                - (from_header.start_padding as usize)
                - (from_header.end_padding as usize);
            std::ptr::copy(from_content_start.as_ptr(), slot, content_size);

            GcPtr {
                start: NonNull::new_unchecked(current as *mut BlockHeader),
            }
        }
    }

    fn contains(&self, ptr: *const BlockHeader) -> bool {
        self.space.contains(ptr)
    }
}

impl MatureSpace {
    pub fn new(_size: usize) -> Self {
        MatureSpace {
            //TODO: heap limit to trigger allocation, or a way to measure (an approx of) current
            //allocations
            space: RefCell::new(AllocState::new()),
        }
    }

    /// Allocates an object in this space, or returns `None` if the space is full.
    pub fn alloc<T: Trace>(&self, data: T) -> Gc<T> {
        unsafe {
            let align = max(align_of::<BlockHeader>(), align_of::<T>());
            let padding = size_of::<BlockHeader>().next_multiple_of(align_of::<T>()) - size_of::<BlockHeader>();
            let mut size = size_of::<BlockHeader>() + size_of::<T>() + padding; 

            Gc {
                start: self.space.borrow_mut().alloc().unwrap(),
                _marker: PhantomData,
            }
        }
    }

    /// De-allocates a block. Caution: currently this doesn't call [Drop::drop], so any heap-allocated
    /// memory will leak. This is to be fixed in the future.
    ///
    /// # Safety
    ///
    /// The backing memory will be de-allocated. The content of the block must thus be "drop-safe"
    /// (not aliased, etc.).
    pub unsafe fn free(&self, mut ptr: NonNull<BlockHeader>) {
        let header = ptr.as_mut();
        //TODO: merge with the following block if it's empty
        *header = BlockHeader::empty(header.size, self.next_free.get());
        self.next_free.set(Some(ptr));
    }

    pub fn parse(&self) {
        for ptr in self.iter() {
            let header = unsafe { &*ptr };
            println!(
                "Next object: {} bytes (header @ {ptr:p}), type: {:?}",
                header.size, header.block_type
            );
        }
    }

    fn iter(&self) -> impl std::iter::Iterator<Item = *mut BlockHeader> {
        HeapSpaceIter {
            curr: self.space.start.as_ptr(),
            end: self.space.end(),
        }
    }

    /// Marking phase of the mark and sweep algorithm. `stack` is providing the list of roots
    /// through [MemoryManager].
    fn mark(&self, stack: &mut MemoryManager) {
        for entry in stack.iter_mut_as_trace_entries() {
            let root = unsafe { *entry.field };
            eprintln!("Tracing root {root:p}");

            let header = unsafe { &mut *(root.as_ptr() as *mut BlockHeader) };
            debug_assert!(
                !header.is_marked(),
                "roots should always be unmarked at the beginning of the tracing phase"
            );
            // Safety: `gc_ptr` is a valid GcPtr created from a mutable reference (that isn't used
            // anymore).
            unsafe { entry.mark() }
        }
    }

    /// Sweeping phase of the mark and sweep algorithm. Free all unmarked blocks, and unmark
    /// previously marked blocks, preparing for the next collection.
    pub fn sweep(&self) {
        let mut ptr = self.space.start.as_ptr();
        let end = self.space.end();

        unsafe {
            while ptr < end {
                // unwrap(): No pointer in the range [start, end] is null
                let header = ptr.cast::<BlockHeader>().as_mut().unwrap();
                if header.is_marked() {
                    println!("Object {ptr:p} is marked. Keeping and unmarking");
                    header.unmark();
                }
                // We must be aware of not freeing already free blocks, which would corrupt the
                // free block list.
                else if matches!(header.block_type, BlockType::Allocated { .. }) {
                    self.free(header.into());
                }

                println!("Next object: {} bytes (header @ {ptr:p})", header.size);
                ptr = ptr.wrapping_add(header.size + size_of::<BlockHeader>());
            }
        }
    }

    pub fn collect(&self, roots: &mut MemoryManager) {
        self.mark(roots);
        self.sweep();
    }
}

impl AllocSpace for MatureSpace {
    fn copy(&self, obj: GcPtr) -> GcPtr {
        // Safety: `obj.start` is a valid, "unaliased" pointer to a block header
        // unwrap(): a `GcPtr` shouldn't point to an empty block
        let layout = unsafe { obj.start.as_ref().layout().unwrap() };
        let Some(free_block) = self.find_fitting_block(layout) else {
            todo!("no space left; trigger a GC");
        };

        eprintln!(
            "alloc(): splitting block at {free_block:p} of size {}",
            unsafe { free_block.as_ref().size }
        );

        let tracer = unsafe { obj.start.as_ref().tracer };
        self.split_block_untyped(free_block, layout, tracer);

        eprintln!("alloc(): block after splitting {:?}", unsafe {
            free_block.as_ref()
        });

        unsafe {
            let align = layout.align();
            let unaligned_slot = free_block.as_ptr().add(1).cast();
            assert!(align * size_of::<u8>() < (isize::MAX as usize));
            let slot = align_up(unaligned_slot, align);

            // Shouldn't be needed: a free block should never overlap with an allocated block
            assert!(!self.space.contains(obj.start.as_ptr()));
            ptr::copy_nonoverlapping(obj.data_ptr().as_ptr(), slot, layout.size());

            GcPtr { start: free_block }
        }
    }

    fn contains(&self, ptr: *const BlockHeader) -> bool {
        self.space.contains(ptr)
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
            .wrapping_add(header.size + size_of::<BlockHeader>());

        Some(next)
    }
}

/// Unsafety: the preconditions to avoid Undefined Behavior are the same as for
/// `std::ptr::wrapping_add`.
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
    ptr.wrapping_add(offset)
}

unsafe fn align_up_cst(ptr: *const u8, align: usize) -> *const u8 {
    // 1. Extract the complement to `align` (same as 2 complement) of `remainder = ptr % align`.
    //    That is `!remainder + 1` which is `align - remainder` if `remainder != 0`, or `align`
    //    otherwise.
    // 2. Take the modulo `align` again to get exactly `align - remainder`
    // 3. Offset the ptr by this value
    let offset = ((!(ptr as usize) & (align - 1)) + 1) & (align - 1);
    ptr.wrapping_add(offset)
}

/// Unsafety: the preconditions to avoid Undefined Behavior are the same as for `std::ptr::add`.
/// This methods keeps the address provenance information.
///
/// Requires that `align` is a power of 2.
unsafe fn align_down(ptr: *mut u8, align: usize) -> *mut u8 {
    let offset = (ptr as usize) & (align - 1);
    ptr.sub(offset)
}

/// Since a moving collector needs to mutably update objects, we face an issue with roots: we can't
/// just return `Gc<T>` pointers to consumers, as they might keep them out of the radar and
/// re-purposing their memory after a young collection would be UB. Instead, all allocations must
/// go through this manager which maps indices to actual GC pointers, adding an indirection.
#[derive(Debug)]
pub struct MemoryManager {
    memory: Vec<Option<GcPtr>>,
}

/// We're keeping heterogenuous data in the manager, but we only indentify them through an index.
/// [StackIndex] keeps an additional type marker to remember the type of the index, so that we can
/// safely convert the "untyped" pointer [Self::GcPtr] that we get back from the manager to an
/// object of the original type.
pub struct GcIndex<T> {
    index: usize,
    _marker: PhantomData<T>,
}

impl<T> Clone for GcIndex<T> {
    fn clone(&self) -> Self {
        Self {
            index: self.index.clone(),
            _marker: PhantomData,
        }
    }
}

impl<T> Copy for GcIndex<T> {}

impl MemoryManager {
    pub fn new() -> Self {
        MemoryManager { memory: Vec::new() }
    }

    pub fn iter(&self) -> impl Iterator<Item = GcPtr> + '_ {
        self.memory.iter().copied().filter_map(|ptr| ptr)
    }

    pub fn iter_index(&self) -> impl Iterator<Item = usize> + '_ {
        self.memory
            .iter()
            .enumerate()
            .filter_map(|(idx, ptr)| ptr.is_some().then_some(idx))
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut GcPtr> {
        self.memory.iter_mut().filter_map(|ptr| ptr.as_mut())
    }

    pub fn root<T: Trace>(&mut self, heap: &Heap, value: T) -> GcIndex<T> {
        if !heap.can_alloc_young::<T>() {
            heap.collect_young(self);
        }

        if let Some(alloced) = heap.alloc_young(value) {
            self.memory.push(Some(alloced.as_gc_ptr()));
            GcIndex {
                index: self.memory.len() - 1,
                _marker: PhantomData,
            }
        } else {
            panic!("out of memory")
        }
    }

    pub fn unroot<T>(&mut self, index: GcIndex<T>) -> bool {
        self.unroot_index(index.index)
    }

    /// # Panics
    ///
    /// Panics if the index is out of bound for this manager.
    pub fn unroot_index(&mut self, index: usize) -> bool {
        let slot = &mut self.memory[index];
        let was_alloced = slot.is_some();
        self.memory[index] = None;
        was_alloced
    }

    pub fn get_weak<T>(&self, index: GcIndex<T>) -> Option<Gc<T>> {
        self.memory[index.index].map(|ptr| Gc {
            start: ptr.start,
            _marker: PhantomData,
        })
    }

    pub fn get<T>(&self, index: GcIndex<T>) -> Gc<T> {
        self.get_weak(index).unwrap()
    }

    /// Iterate over the live roots of this memory manager seen as trace entries.
    fn iter_mut_as_trace_entries(&mut self) -> impl Iterator<Item = TraceEntry> + '_ {
        self.iter_mut().map(|gc_ptr| TraceEntry {
            field: &mut gc_ptr.start as *mut NonNull<BlockHeader>,
        })
    }
}

impl<T> fmt::Pointer for Gc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:p}", self.start)
    }
}

impl fmt::Pointer for GcPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:p}", self.start)
    }
}
