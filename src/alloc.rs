//! Memory allocator for the mature space / mark-and-sweep collector. WIP: for new the GC uses the
//! simpler linked-list allocator implemented in [super::MatureSpace]. The goal is to replace it
//! with this one, which is a more modern version with small fixed-size classes and an all-purpose
//! best-fit one for bigger objects.

// use bitmaps::{Bitmap, Bits, BitsImpl};
use memmap::{self, MmapMut};
use std::{alloc::Layout, io, ptr::NonNull};

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

struct AllocBucket
{
    pages: MmapMut,
    block_size: usize,
    allocated: Bitmap,
    marked: Bitmap,
    next: Option<NonNull<AllocBucket>>,
    prev: Option<NonNull<AllocBucket>>,
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


impl AllocBucket
{
    pub fn new(block_size: usize) -> Self {
        Self {
            pages: alloc_page().unwrap(),
            block_size,
            allocated: Bitmap::new(block_size),
            marked: Bitmap::new(block_size),
            next: None,
            prev: None,
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
}

struct Classes {
    data: [NonNull<u8>; 9],
}

struct AllocState {
    buckets: [AllocBucket; 9],
}

impl AllocState {
    pub fn new() -> Self {
        Self {
            buckets: std::array::from_fn(|index| {
                AllocBucket::new(1 << (index + 3)) 
            }),
        }
    }

    pub fn alloc(&mut self, layout: Layout) -> Option<*mut u8> {
        todo!() 
    }

    pub fn free(&mut self, addr: *const u8) {
        todo!() 
    }
}
