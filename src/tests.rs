use crate::{Gc, GcIndex, Heap, MemoryManager, Trace};
use arbitrary::{Arbitrary, Unstructured};
use arbtest::arbtest;
use std::cmp::min;

#[derive(Arbitrary)]
enum Data {
    IntPayload(i32),
    ArrayPayload([u8; 10]),
    None,
}

struct ManagedObject {
    children: Vec<Gc<ManagedObject>>,
    data: Data,
}

impl Trace for ManagedObject {
    fn trace(&mut self, stack: &mut Vec<crate::TraceEntry>) {
        stack.extend(self.children.iter_mut().map(Gc::as_trace_entry));
    }
}

const MAX_CHILDREN: usize = 8;
const MAX_CHUNK_SIZE: usize = 20;
const UNROOT_RATIO: (usize, usize) = (1, 2);

const SPACE_SIZE: usize = 1024 * 1024;

impl ManagedObject {
    /// Allocate a new managed object, that randomly includes some of the existing allocated
    /// objects as children, and with random payloads. The object is directly allocated in the
    /// memory manager.
    ///
    /// # Safety
    ///
    /// This function requires that only [ManagedObject] are currently allocated in the memory
    /// manager.
    pub fn alloc_random(
        u: &mut Unstructured,
        heap: &Heap,
        manager: &mut MemoryManager,
    ) -> Result<(), arbitrary::Error> {
        let alloc_count = manager.iter().count();

        let children_count = u.int_in_range(0..=min(alloc_count, MAX_CHILDREN))?;
        let mut children = Vec::with_capacity(children_count);

        // TODO: get rid of this collection. We need it as long as we haven't fix the issue of
        // GcPtr taken in the for loop being invalidated later by `root` causing a collection when
        // space is insufficient.
        if !heap.can_alloc_young::<ManagedObject>() {
            heap.collect_young(manager);
        }

        let allocs: Vec<_> = manager.iter().collect();

        for _ in 0..children_count {
            // Safety: this is the safety precondition of this function.
            let child = unsafe { Gc::<ManagedObject>::from_gc_ptr(*u.choose(&allocs)?) };
            children.push(child);
        }

        let data = Data::arbitrary(u)?;
        manager.root(heap, ManagedObject { children, data });
        Ok(())
    }
}

fn alloc_bulk(
    u: &mut Unstructured,
    heap: &Heap,
    manager: &mut MemoryManager,
) -> Result<(), arbitrary::Error> {
    let chunk_size = u.int_in_range(0..=MAX_CHUNK_SIZE)?;

    for _ in 0..chunk_size {
        ManagedObject::alloc_random(u, heap, manager)?;
    }

    Ok(())
}

fn unroot_bulk(u: &mut Unstructured, manager: &mut MemoryManager) -> Result<(), arbitrary::Error> {
    let alloc_count = manager.iter().count();

    if alloc_count == 0 {
        return Ok(());
    }

    let unroot_count = UNROOT_RATIO.0 * alloc_count / UNROOT_RATIO.1;
    let indices: Vec<_> = manager.iter_index().collect();

    for _ in 0..=unroot_count {
        let index = u.choose(&indices)?;
        manager.unroot_index(*index);
    }

    Ok(())
}

#[test]
fn tree_one_round_manual_young_collect() {
    arbtest(|u| {
        let heap = Heap::new(SPACE_SIZE, SPACE_SIZE);
        let mut manager = MemoryManager::new();

        alloc_bulk(u, &heap, &mut manager)?;
        unroot_bulk(u, &mut manager)?;
        heap.collect_young(&mut manager);
        Ok(())
    });
}

#[test]
fn tree_multi_rounds_manual_young_collect() {
    arbtest(|u| {
        let heap = Heap::new(SPACE_SIZE, SPACE_SIZE);
        let mut manager = MemoryManager::new();

        alloc_bulk(u, &heap, &mut manager)?;
        unroot_bulk(u, &mut manager)?;
        heap.collect_young(&mut manager);
        alloc_bulk(u, &heap, &mut manager)?;
        unroot_bulk(u, &mut manager)?;
        heap.collect_young(&mut manager);
        alloc_bulk(u, &heap, &mut manager)?;
        unroot_bulk(u, &mut manager)?;
        heap.collect_young(&mut manager);

        Ok(())
    });
}

#[test]
fn tree_young_collecs() {
    arbtest(|u| {
        let heap = Heap::new(size_of::<ManagedObject>() * 5, SPACE_SIZE);
        let mut manager = MemoryManager::new();

        alloc_bulk(u, &heap, &mut manager)?;
        unroot_bulk(u, &mut manager)?;

        alloc_bulk(u, &heap, &mut manager)?;
        unroot_bulk(u, &mut manager)?;

        alloc_bulk(u, &heap, &mut manager)?;
        unroot_bulk(u, &mut manager)?;

        Ok(())
    });
}

#[test]
fn tree_young_collecs_and_mature() {
    arbtest(|u| {
        let heap = Heap::new(size_of::<ManagedObject>() * 5, SPACE_SIZE);
        let mut manager = MemoryManager::new();

        alloc_bulk(u, &heap, &mut manager)?;
        unroot_bulk(u, &mut manager)?;

        alloc_bulk(u, &heap, &mut manager)?;
        unroot_bulk(u, &mut manager)?;

        alloc_bulk(u, &heap, &mut manager)?;
        unroot_bulk(u, &mut manager)?;

        heap.collect_mature(&mut manager);

        Ok(())
    });
}
