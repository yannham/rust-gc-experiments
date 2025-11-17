//! Memory allocator for the mature space / mark-and-sweep collector. WIP: for new the GC uses the
//! simpler linked-list allocator implemented in [super::MatureSpace]. The goal is to replace it
//! with this one, which is a more modern version with small fixed-size classes and an all-purpose
//! best-fit one for bigger objects.

use bitmaps::{Bitmap, Bits, BitsImpl};
use memmap::{self, MmapMut};
use std::{alloc::Layout, io};

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

const SMALL_CLASS_SIZES: [usize; 3] = [8, 16, 32];
const PAGE_SIZE: usize = 4 * 1024;

fn alloc_page() -> io::Result<MmapMut> {
    MmapMut::map_anon(PAGE_SIZE)
}

struct AllocBucket<const SIZE: usize>
where
    BitsImpl<{ SIZE }>: Bits,
{
    pages: MmapMut,
    allocated: Bitmap<SIZE>,
    marked: Bitmap<SIZE>,
}

impl<const SIZE: usize> AllocBucket<SIZE>
where
    BitsImpl<{ SIZE }>: Bits,
{
    pub fn new() -> Self {
        Self {
            pages: alloc_page().unwrap(),
            allocated: Bitmap::new(),
            marked: Bitmap::new(),
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
        unsafe { Some(self.base_mut().add(slot_index * SIZE)) }
    }

    pub fn free(&mut self, addr: *const u8) {
        let base = self.base();

        unsafe {
            assert!(self.contains(addr), "error: tried to free an adress outside of the bucket ({addr:p}, bucket start: {base:p})");
        }
        let slot_index = ((addr as usize) - (base as usize)) / SIZE;

        assert!(
            self.allocated.get(slot_index),
            "error: double-free @ {addr:p} (class size {SIZE})"
        );

        self.allocated.set(slot_index, false);
    }
}

const fn bitmap_size(obj_size: usize) -> usize {
    PAGE_SIZE / obj_size
}

struct AllocState {
    class8: AllocBucket<{ PAGE_SIZE / 8 }>,
    class16: AllocBucket<{ PAGE_SIZE / 16 }>,
    class32: AllocBucket<{ PAGE_SIZE / 32 }>,
}

impl AllocState {
    pub fn new() -> Self {
        Self {
            class8: AllocBucket::new(),
            class16: AllocBucket::new(),
            class32: AllocBucket::new(),
        }
    }

    pub fn alloc(&mut self, layout: Layout) -> Option<*mut u8> {
        if layout.size() <= 8 && layout.align() <= 8 {
            self.class8.alloc()
        } else if layout.size() <= 16 && layout.align() <= 16 {
            self.class16.alloc()
        } else if layout.size() <= 32 && layout.align() <= 32 {
            self.class32.alloc()
        } else {
            todo!()
        }
    }

    pub fn free(&mut self, addr: *const u8) {
        if self.class8.contains(addr) {
            self.class8.free(addr)
        } else if self.class16.contains(addr) {
            self.class16.free(addr)
        } else if self.class32.contains(addr) {
            self.class32.free(addr)
        } else {
            todo!()
        }
    }
}
