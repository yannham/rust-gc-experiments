//! Memory allocator for the mature space / mark-and-sweep collector. WIP: for new the GC uses the
//! simpler linked-list allocator implemented in [super::MatureSpace]. The goal is to replace it
//! with this one, which is a more modern version with small fixed-size classes and an all-purpose
//! best-fit one for bigger objects.

// use bitmaps::{Bitmap, Bits, BitsImpl};
use memmap::{self, MmapMut};
use std::{
    alloc::Layout,
    cmp::max,
    io,
    mem::{self, ManuallyDrop},
    ptr::{self, NonNull},
};

// ALLOCATOR DESIGN
//
// 8/16/32: tiny allocations - separate allocation bitmap
// We start with initial k pages for each. Request more pages to the OS as we go.
//
// a bunch of `n` pages for each size. If need more pages, we alloc them. we have a linked of
// metadata for each page, which points back to the first byte of the page. Each page has also a
// pointer back to the its metadata (could also fit the bitmap in the page, but beware of cache
// associativity).
//
// Allocation path (for fixed-size classes):
//  - find the right size class
//  - find the first non-full page
//  - find the first empty slot in the bitmap
//  - alloc and return it
//  - set the bit to 1
//
// On de-allocation:
//  - find the page metadata from a pointer
//  - set the bit in the bitmap to 0
//  - if the page was full, put it at the end of the non-full list
//  - if the page is empty, and the current number of allocated pages is > k + p, then return it
//    to the OS
//
// Non-fixed size bucket: start with one big block, and split it in two each time. Keep the
// available free blocks in a ordered tree. Find the best fit, remove it from the tree, and return
// it.
//
// TODO: look at the bit/binary/buddy algorithm to recombine blocks. That would happen upon
// freeing.
//
// The question of where to put the mark bit? Probably in a bitmap for fixed-size value, and in a
// header maybe for others? Or all in bitmap?
//
// TODO: why the interface of alloc is Option<*mut u8>?

const PAGE_SIZE: usize = 4 * 1024;

fn alloc_page() -> io::Result<MmapMut> {
    MmapMut::map_anon(PAGE_SIZE)
}

struct BucketList {
    bucket: AllocBucket,
    next: Option<NonNull<BucketList>>,
    prev: Option<NonNull<BucketList>>,
}

impl BucketList {
    pub fn new(bucket: AllocBucket) -> NonNull<Self> {
        unsafe {
            NonNull::new_unchecked(Box::into_raw(Box::new(Self {
                bucket,
                next: None,
                prev: None,
            })))
        }
    }

    pub fn prepend(mut head: NonNull<BucketList>, bucket: AllocBucket) -> NonNull<Self> {
        let bucket = Self {
            bucket,
            next: Some(head),
            prev: None,
        };

        let new_node = unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(bucket))) };

        unsafe {
            assert!(head.as_ref().prev.is_none());
            head.as_mut().prev = Some(new_node);
        }

        new_node
    }

    pub fn alloc(head: NonNull<Self>) -> Option<NonNull<u8>> {
        let mut node = Self::find_first(head, |node| !node.bucket.is_full())?;
        unsafe { node.as_mut().bucket.alloc() }
    }

    pub fn free(this: NonNull<Self>, addr: *const u8) {
        //TODO: if we end up with an empty page, we probably want to either release it, or put it
        //in front, etc.
        //TODO: we have to search for the right page in the list. We could maybe find the address
        //of the page directly from `addr` (easy), and have a way to go from a page addr to
        //metadata addr (for example, write the address of the corresponding node in the first slot
        //of the page)
        let Some(mut node) = Self::find_first(this, |node| node.bucket.contains(addr)) else {
            panic!("couldn't find address {addr:p} in its class size's buckets");
        };
        unsafe { node.as_mut().bucket.free(addr) }
    }

    pub fn find_first(
        head: NonNull<Self>,
        mut pred: impl FnMut(&BucketList) -> bool,
    ) -> Option<NonNull<BucketList>> {
        let mut curr = head;

        unsafe {
            while !pred(curr.as_ref()) {
                curr = curr.as_ref().next?;
            }
        }

        Some(curr)
    }
}

struct AllocBucket {
    pages: MmapMut,
    block_size: usize,
    allocated: Bitmap,
    marked: Bitmap,
}

const fn bitmap_size(size: usize) -> usize {
    PAGE_SIZE / size
}

struct Bitmap(Vec<bool>);

impl Bitmap {
    pub fn new(block_size: usize) -> Self {
        Bitmap(vec![false; block_size])
    }

    pub fn first_false_index(&self) -> Option<usize> {
        self.0.iter().position(|b| !*b)
    }

    pub fn get(&self, index: usize) -> bool {
        self.0[index]
    }

    pub fn set(&mut self, index: usize, bit: bool) {
        self.0[index] = bit
    }
}

impl AllocBucket {
    pub fn new(block_size: usize) -> Self {
        Self {
            pages: alloc_page().unwrap(),
            block_size,
            allocated: Bitmap::new(block_size),
            marked: Bitmap::new(block_size),
        }
    }

    fn base_mut(&mut self) -> NonNull<u8> {
        unsafe { NonNull::new_unchecked(self.pages.as_mut_ptr()) }
    }

    fn base(&self) -> *const u8 {
        self.pages.as_ptr()
    }

    pub fn contains(&self, addr: *const u8) -> bool {
        let base = self.base();
        base < addr && addr < base.wrapping_add(PAGE_SIZE)
    }

    pub fn alloc(&mut self) -> Option<NonNull<u8>> {
        let slot_index = self.allocated.first_false_index()?;

        self.allocated.set(slot_index, true);
        unsafe { Some(self.base_mut().add(slot_index * self.block_size)) }
    }

    pub fn free(&mut self, addr: *const u8) {
        let base = self.base();

        assert!(self.contains(addr), "error: tried to free an adress outside of the bucket ({addr:p}, bucket start: {base:p})");
        let slot_index = ((addr as usize) - (base as usize)) / self.block_size;

        assert!(
            self.allocated.get(slot_index),
            "error: double-free @ {addr:p} (class size {})",
            self.block_size
        );

        self.allocated.set(slot_index, false);
    }

    pub fn is_full(&self) -> bool {
        self.allocated.0.iter().all(|bit| *bit)
    }
}

/// The header that we write at the beginning of a big allocation. Freeing is just dropping this
/// header; the [Drop] implementation of [MmapMut] will return the pages to the OS.
struct BigAllocHeader {
    pages: MmapMut,
}

pub struct AllocState {
    buckets: [NonNull<BucketList>; 9],
}

impl AllocState {
    pub fn new() -> Self {
        Self {
            buckets: std::array::from_fn(|index| {
                BucketList::new(AllocBucket::new(1 << (index + 3)))
            }),
        }
    }

    pub fn alloc(&mut self, layout: Layout) -> Option<NonNull<u8>> {
        if let Some(idx) = Self::index(&layout) {
            self.small_alloc(idx)
        } else {
            self.big_alloc(layout)
        }
    }

    pub fn small_alloc(&mut self, idx: usize) -> Option<NonNull<u8>> {
        BucketList::alloc(self.buckets[idx]).or_else(|| {
            let mut new_bucket = AllocBucket::new(1 << (idx + 3));
            let alloced = new_bucket.alloc();
            self.buckets[idx] = BucketList::prepend(self.buckets[idx], new_bucket);
            alloced
        })
    }

    pub fn big_alloc(&mut self, layout: Layout) -> Option<NonNull<u8>> {
        assert!(layout.align() <= PAGE_SIZE);

        // We write the `MmapMut` corresponding object at the end of the allocation, as raw bytes
        // (in the sense that we will never materialize any reference to it in-place, so we don't
        // have to care about alignement). When freeing, we reconstruct this object and simply drop
        // it.
        let total_size = layout.size() + mem::size_of::<MmapMut>();
        let mut pages = ManuallyDrop::new(MmapMut::map_anon(total_size).ok()?);
        unsafe {
            pages
                .as_mut_ptr()
                // SAFETY:
                .add(layout.size())
                .copy_from_nonoverlapping(
                    &pages as *const _ as *const u8,
                    mem::size_of::<MmapMut>(),
                );

            //SAFETY: an mmaped region is never null
            Some(NonNull::new_unchecked(pages.as_mut_ptr()))
        }
    }

    pub fn free(&mut self, addr: *const u8, layout: Layout) {
        if let Some(idx) = Self::index(&layout) {
            BucketList::free(self.buckets[idx], addr)
        } else {
            self.free_big(addr, layout);
        }
    }

    fn free_big(&mut self, addr: *const u8, layout: Layout) {
        let mut pages: mem::MaybeUninit<MmapMut> = mem::MaybeUninit::uninit();
        // SAFETY: for big allocation, we add a raw copy of the MmapMut object at the end of
        // the allocation
        unsafe {
            ptr::copy_nonoverlapping(
                addr.add(layout.size()),
                pages.as_mut_ptr() as *mut u8,
                mem::size_of::<MmapMut>(),
            );

            // Just drop the mmap mut will run the destructor and return the pages to the OS
            pages.assume_init();
        }
    }

    fn index(layout: &Layout) -> Option<usize> {
        let form_factor = max(layout.size(), layout.align());
        let upper_bound = form_factor.next_power_of_two().ilog2() as usize;

        // Small alloc are maxed at 2KB, which is `2^11`
        if upper_bound > 11 {
            None
        } else {
            Some(upper_bound.saturating_sub(3))
        }
    }
}
