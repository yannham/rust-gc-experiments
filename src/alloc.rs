//! Memory allocator for the mature space / mark-and-sweep collector. WIP: for new the GC uses the
//! simpler linked-list allocator implemented in [super::MatureSpace]. The goal is to replace it
//! with this one, which is a more modern version with small fixed-size classes and an all-purpose
//! best-fit one for bigger objects.

// use bitmaps::{Bitmap, Bits, BitsImpl};
use memmap::{self, MmapMut};
use std::{alloc::Layout, cmp::max, io, ptr::NonNull};

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

    pub fn alloc(head: NonNull<Self>) -> Option<*mut u8> {
        let mut node = Self::find_first(head, |node| !node.bucket.is_full())?;
        unsafe { node.as_mut().bucket.alloc() }
    }

    pub fn free(this: NonNull<Self>, addr: *const u8) {
        //TODO: if we end up with an empty page, we probably want to either release it, or put it
        //in front, etc.
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
        todo!()
    }

    pub fn first_false_index(&self) -> Option<usize> {
        todo!()
    }

    pub fn get(&self, index: usize) -> bool {
        todo!()
    }

    pub fn set(&mut self, index: usize, bit: bool) {
        todo!()
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

    fn base_mut(&mut self) -> *mut u8 {
        self.pages.as_mut_ptr()
    }

    fn base(&self) -> *const u8 {
        self.pages.as_ptr()
    }

    pub fn contains(&self, addr: *const u8) -> bool {
        let base = self.base() as *const u8;
        // Safety: TODO
        unsafe { base < addr && addr < base.add(PAGE_SIZE) }
    }

    pub fn alloc(&mut self) -> Option<*mut u8> {
        let slot_index = self.allocated.first_false_index()?;

        self.allocated.set(slot_index, true);
        unsafe { Some(self.base_mut().add(slot_index * self.block_size)) }
    }

    pub fn free(&mut self, addr: *const u8) {
        let base = self.base();

        unsafe {
            assert!(self.contains(addr), "error: tried to free an adress outside of the bucket ({addr:p}, bucket start: {base:p})");
        }
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

struct Classes {
    data: [NonNull<u8>; 9],
}

struct AllocState {
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

    pub fn alloc(&mut self, layout: Layout) -> Option<*mut u8> {
        if let Some(idx) = Self::index(&layout) {
            BucketList::alloc(self.buckets[idx]).or_else(|| {
                let mut new_bucket = AllocBucket::new(1 << (idx + 3));
                let alloced = new_bucket.alloc();
                self.buckets[idx] = BucketList::prepend(self.buckets[idx], new_bucket);
                alloced
            })
        } else {
            todo!()
        }
    }

    pub fn free(&mut self, addr: *const u8, layout: Layout) {
        if let Some(idx) = Self::index(&layout) {
            BucketList::free(self.buckets[idx], addr)
        } else {
            todo!()
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
