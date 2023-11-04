use std::{
    collections::hash_map::RandomState,
    fmt::Debug,
    hash::{BuildHasher, Hash},
    num::NonZeroUsize,
};

use hashbrown::{
    raw::{InsertSlot, RawTable},
    Equivalent,
};

#[derive(Debug, PartialEq, Clone, Copy)]
struct DataIndex {
    data: usize,
}
#[derive(Debug, PartialEq, Clone, Copy)]
struct TtlHeapIndex {
    ttl_heap: usize,
}
#[derive(Debug, PartialEq, Clone, Copy)]
struct LruHeapIndex {
    lru_heap: usize,
}

pub struct TtlMap<K, V, T> {
    hasher: RandomState,

    map: RawTable<DataIndex>,

    // in theory I could push this into map
    // but I would have to rewrite my own RawTable as I can't access swap information
    data: Vec<(K, V, TtlHeapIndex, LruHeapIndex)>,

    ttl_heap: Vec<(T, DataIndex)>,
    lru_heap: Vec<(usize, DataIndex)>,
    capacity: NonZeroUsize,
    epoch: usize,
}

impl<K: core::fmt::Debug, V: core::fmt::Debug, T: core::fmt::Debug> core::fmt::Debug
    for TtlMap<K, V, T>
{
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        struct Map<'a> {
            map: &'a RawTable<DataIndex>,
        }

        impl core::fmt::Debug for Map<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_list()
                    .entries(unsafe { self.map.iter().map(|i| i.as_ref()) })
                    .finish()
            }
        }

        f.debug_struct("TtlMap2")
            .field("hasher", &self.hasher)
            .field("map", &Map { map: &self.map })
            .field("data", &self.data)
            .field("ttl", &self.ttl_heap)
            .field("lru", &self.lru_heap)
            .field("capacity", &self.capacity)
            .finish()
    }
}

impl<K: Hash + Eq, V, T: Ord + Copy> TtlMap<K, V, T> {
    // // find the entry that is next to expire
    // fn peek_front(&self, now: Instant) -> Option<usize> {
    //     let (time, space) = *self.heap.first()?;
    //     (time < now).then_some(space)
    // }

    pub fn with_capacity(capacity: NonZeroUsize) -> Self {
        TtlMap {
            hasher: RandomState::new(),
            map: RawTable::with_capacity(capacity.get()),
            data: Vec::with_capacity(capacity.get()),
            ttl_heap: Vec::with_capacity(capacity.get()),
            lru_heap: Vec::with_capacity(capacity.get()),
            capacity,
            epoch: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.ttl_heap.len()
    }

    pub fn capacity(&self) -> NonZeroUsize {
        self.capacity
    }

    pub fn set_capacity(&mut self, capacity: NonZeroUsize) {
        if self.capacity < capacity {
            self.data.reserve(capacity.get() - self.data.len());
            self.ttl_heap.reserve(capacity.get() - self.ttl_heap.len());
            self.lru_heap.reserve(capacity.get() - self.lru_heap.len());
            self.map.reserve(capacity.get() - self.map.len(), |&idx| {
                self.hasher.hash_one(&self.data[idx.data].0)
            });
        }
        self.capacity = capacity;
    }

    pub fn is_empty(&self) -> bool {
        self.ttl_heap.is_empty()
    }

    pub fn is_full(&self) -> bool {
        self.len() == self.capacity.get()
    }

    pub fn clear(&mut self) {
        self.epoch = 0;
        self.data.clear();
        self.map.clear();
        self.lru_heap.clear();
        self.ttl_heap.clear();
    }

    /// evicts all expired entries
    /// will re-position elements in the map
    fn evict(&mut self, now: T) {
        while self.evict_ttl_one(now) {}
        if self.is_full() {
            self.evict_lru();
        }
    }

    /// evicts a single expired entry from the map.
    /// will re-position elements in the map
    fn evict_ttl_one(&mut self, now: T) -> bool {
        let Some(&(expires, data_idx)) = self.ttl_heap.first() else {
            return false;
        };

        if expires > now {
            return false;
        }

        // remove data from map

        let (key, _, ttl_evicted, lru_evicted) = self.data.swap_remove(data_idx.data);
        debug_assert_eq!(ttl_evicted.ttl_heap, 0);

        let hash = self.hasher.hash_one(&key);
        self.map
            .remove_entry(hash, |&idx| idx.data == data_idx.data)
            .unwrap();

        self.remove_inner(data_idx, ttl_evicted, lru_evicted);

        // let heap_evicted = TtlHeapIndex { ttl_heap: 0 };
        // let (_, data_evicted) = self.ttl_heap.swap_remove(heap_evicted.ttl_heap);
        // // fix data -> heap
        // if let Some(&(_, data_idx)) = self.ttl_heap.get(heap_evicted.ttl_heap) {
        //     let _old_heap_idx = std::mem::replace(&mut self.data[data_idx.data].2, heap_evicted);
        //     debug_assert_eq!(_old_heap_idx.ttl_heap, self.ttl_heap.len());
        // }

        // let (key, _, _ttl_evicted, lru_evicted) = self.data.swap_remove(data_evicted.data);
        // debug_assert_eq!(_ttl_evicted.ttl_heap, 0);

        // self.lru_heap.swap_remove(lru_evicted.lru_heap);
        // self.lru_downheap(self.lru_heap[lru_evicted.lru_heap].0, lru_evicted);

        // if let Some(&(ref key, _, ttl_idx, lru_idx)) = self.data.get(data_evicted.data) {
        //     // fix map -> data
        //     let hash = self.hasher.hash_one(key);
        //     *self
        //         .map
        //         .get_mut(hash, |&idx| idx.data == self.data.len())
        //         .unwrap() = data_evicted;

        //     // fix heap -> data
        //     let _old_data_idx =
        //         std::mem::replace(&mut self.ttl_heap[ttl_idx.ttl_heap].1, data_evicted);
        //     debug_assert_eq!(_old_data_idx.data, self.data.len());
        //     let _old_data_idx =
        //         std::mem::replace(&mut self.lru_heap[lru_idx.lru_heap].1, data_evicted);
        //     debug_assert_eq!(_old_data_idx.data, self.data.len());
        // }

        // if self.ttl_heap.is_empty() {
        //     return false;
        // }

        // // push down the entry we swapped
        // let heap_idx = self.ttl_downheap(self.ttl_heap[0].0, TtlHeapIndex { ttl_heap: 0 });

        // // fix data -> heap
        // let data_idx = self.ttl_heap[heap_idx.ttl_heap].1;
        // self.data[data_idx.data].2 = heap_idx;

        true
    }

    /// evicts the least recently used element.
    /// will re-position elements in the map
    fn evict_lru(&mut self) {
        let Some(&(_, data_idx)) = self.lru_heap.first() else {
            return;
        };

        let (key, _, ttl_evicted, lru_evicted) = self.data.swap_remove(data_idx.data);
        debug_assert_eq!(lru_evicted.lru_heap, 0);

        let hash = self.hasher.hash_one(&key);
        self.map
            .remove_entry(hash, |&idx| idx.data == data_idx.data)
            .unwrap();

        self.remove_inner(data_idx, ttl_evicted, lru_evicted);

        // let heap_evicted = LruHeapIndex { lru_heap: 0 };
        // let (_, data_evicted) = self.lru_heap.swap_remove(heap_evicted.lru_heap);
        // // fix data -> heap
        // if let Some(&(_, data_idx)) = self.lru_heap.get(heap_evicted.lru_heap) {
        //     let _old_heap_idx = std::mem::replace(&mut self.data[data_idx.data].3, heap_evicted);
        //     debug_assert_eq!(_old_heap_idx.lru_heap, self.lru_heap.len());
        // }

        // let (key, _, ttl_evicted, _lru_evicted) = self.data.swap_remove(data_evicted.data);
        // debug_assert_eq!(_lru_evicted.lru_heap, 0);

        // self.ttl_heap.swap_remove(ttl_evicted.ttl_heap);
        // self.ttl_downheap(self.ttl_heap[ttl_evicted.ttl_heap].0, ttl_evicted);

        // // remove data from map
        // let hash = self.hasher.hash_one(&key);
        // self.map
        //     .remove_entry(hash, |&idx| idx.data == data_evicted.data)
        //     .unwrap();

        // if let Some(&(ref key, _, ttl_idx, lru_idx)) = self.data.get(data_evicted.data) {
        //     // fix map -> data
        //     let hash = self.hasher.hash_one(key);
        //     *self
        //         .map
        //         .get_mut(hash, |&idx| idx.data == self.data.len())
        //         .unwrap() = data_evicted;

        //     // fix heap -> data
        //     let _old_data_idx =
        //         std::mem::replace(&mut self.ttl_heap[ttl_idx.ttl_heap].1, data_evicted);
        //     debug_assert_eq!(_old_data_idx.data, self.data.len());
        //     let _old_data_idx =
        //         std::mem::replace(&mut self.lru_heap[lru_idx.lru_heap].1, data_evicted);
        //     debug_assert_eq!(_old_data_idx.data, self.data.len());
        // }

        // if self.lru_heap.is_empty() {
        //     return;
        // }

        // // push down the entry we swapped
        // let heap_idx = self.lru_downheap(self.lru_heap[0].0, LruHeapIndex { lru_heap: 0 });

        // // fix data -> heap
        // let data_idx = self.lru_heap[heap_idx.lru_heap].1;
        // self.data[data_idx.data].3 = heap_idx;
    }

    /// move a new element that has a larger TTL down the heap
    /// will not re-position elements in the map
    fn ttl_downheap(&mut self, expires: T, mut i: TtlHeapIndex) -> TtlHeapIndex {
        loop {
            let left = TtlHeapIndex {
                ttl_heap: 2 * i.ttl_heap + 1,
            };
            let right = TtlHeapIndex {
                ttl_heap: 2 * i.ttl_heap + 2,
            };

            let mut largest = i;
            if left.ttl_heap < self.ttl_heap.len() && self.ttl_heap[left.ttl_heap].0 < expires {
                largest = left
            }
            if right.ttl_heap < self.ttl_heap.len() && self.ttl_heap[right.ttl_heap].0 < expires {
                largest = right
            }

            if largest == i {
                break i;
            }

            let data_idx = self.ttl_heap[largest.ttl_heap].1;
            self.data[data_idx.data].2 = i;

            self.ttl_heap.swap(i.ttl_heap, largest.ttl_heap);
            i = largest;
        }
    }

    /// move a new element that has a shorter TTL up the heap.
    /// will not re-position elements in the map
    fn ttl_upheap(&mut self, expires: T, mut i: TtlHeapIndex) -> TtlHeapIndex {
        while i.ttl_heap > 0 {
            let parent = TtlHeapIndex {
                ttl_heap: (i.ttl_heap - 1) / 2,
            };

            // check if we need to continue
            if expires > self.ttl_heap[parent.ttl_heap].0 {
                break;
            }

            let data_idx = self.ttl_heap[parent.ttl_heap].1;
            self.data[data_idx.data].2 = i;

            self.ttl_heap.swap(i.ttl_heap, parent.ttl_heap);
            i = parent;
        }
        i
    }

    /// move a new element that has a larger TTL down the heap
    /// will not re-position elements in the map
    fn lru_downheap(&mut self, last_access: usize, mut i: LruHeapIndex) -> LruHeapIndex {
        loop {
            let left = LruHeapIndex {
                lru_heap: 2 * i.lru_heap + 1,
            };
            let right = LruHeapIndex {
                lru_heap: 2 * i.lru_heap + 2,
            };

            let mut largest = i;
            if left.lru_heap < self.lru_heap.len() && self.lru_heap[left.lru_heap].0 < last_access {
                largest = left
            }
            if right.lru_heap < self.lru_heap.len() && self.lru_heap[right.lru_heap].0 < last_access
            {
                largest = right
            }

            if largest == i {
                break i;
            }

            let data_idx = self.lru_heap[largest.lru_heap].1;
            self.data[data_idx.data].3 = i;

            self.lru_heap.swap(i.lru_heap, largest.lru_heap);
            i = largest;
        }
    }

    /// move a new element that has a shorter TTL up the heap.
    /// will not re-position elements in the map
    fn lru_upheap(&mut self, last_access: usize, mut i: LruHeapIndex) -> LruHeapIndex {
        while i.lru_heap > 0 {
            let parent = LruHeapIndex {
                lru_heap: (i.lru_heap - 1) / 2,
            };

            // check if we need to continue
            if last_access > self.lru_heap[parent.lru_heap].0 {
                break;
            }

            let data_idx = self.lru_heap[parent.lru_heap].1;
            self.data[data_idx.data].3 = i;

            self.lru_heap.swap(i.lru_heap, parent.lru_heap);
            i = parent;
        }
        i
    }

    pub fn insert(&mut self, now: T, key: K, value: V, expires: T) -> Option<V> {
        let hash = self.hasher.hash_one(&key);

        let slot = if self.is_full() {
            match self.map.find(hash, |&idx| self.data[idx.data].0 == key) {
                // we are at capacity but we will replace an existing entry
                Some(bucket) => Ok(bucket),
                // we will overflow capacity. evict
                None => {
                    self.evict(now);
                    debug_assert!(!self.is_full());
                    // it is guaranteed that
                    // 1. our element is not in the hashtable (find returned None)
                    // 2. there is space in the hashtable (we called evict)
                    unsafe { Err(self.insert_slot_no_grow(hash)) }
                }
            }
        } else {
            self.map.find_or_find_insert_slot(
                hash,
                |&idx| self.data[idx.data].0 == key,
                |&idx| self.hasher.hash_one(&self.data[idx.data].0),
            )
        };

        let epoch = self.epoch;
        self.epoch += 1;

        match slot {
            Ok(bucket) => {
                // SAFETY: we haven't updated the hashtable so this bucket still points to the correct place
                let data_idx = unsafe { *bucket.as_ref() };

                self.data[data_idx.data].0 = key;
                let old_value = std::mem::replace(&mut self.data[data_idx.data].1, value);
                let ttl_idx = self.data[data_idx.data].2;
                let lru_idx = self.data[data_idx.data].3;

                let would_expire = self.ttl_heap[ttl_idx.ttl_heap].0;
                let heap_idx = if would_expire < expires {
                    self.ttl_downheap(expires, ttl_idx)
                } else {
                    self.ttl_upheap(expires, ttl_idx)
                };

                let old_epoch = self.lru_heap[lru_idx.lru_heap].0;
                self.lru_heap[lru_idx.lru_heap].0 = epoch;
                if old_epoch < epoch {
                    self.lru_downheap(epoch, lru_idx);
                } else {
                    self.lru_upheap(epoch, lru_idx);
                }

                // fix data -> heap
                let data_idx = self.ttl_heap[heap_idx.ttl_heap].1;
                self.data[data_idx.data].2 = heap_idx;

                Some(old_value)
            }
            Err(slot) => {
                let ttl_idx = TtlHeapIndex {
                    ttl_heap: self.ttl_heap.len(),
                };
                let lru_idx = LruHeapIndex {
                    lru_heap: self.lru_heap.len(),
                };
                let data_idx = DataIndex {
                    data: self.data.len(),
                };

                // TODO: push_within_capacity?
                self.ttl_heap.push((expires, data_idx));
                self.lru_heap.push((epoch, data_idx));
                self.data.push((key, value, ttl_idx, lru_idx));

                // SAFETY: we haven't updated the hashtable positions so this slot still points to the correct place
                unsafe { self.map.insert_in_slot(hash, slot, data_idx) };

                let ttl_idx = self.ttl_upheap(expires, ttl_idx);
                let lru_idx = self.lru_upheap(epoch, lru_idx);

                // fix data -> heap
                let data_idx = self.ttl_heap[ttl_idx.ttl_heap].1;
                self.data[data_idx.data].2 = ttl_idx;

                let data_idx = self.lru_heap[lru_idx.lru_heap].1;
                self.data[data_idx.data].3 = lru_idx;

                None
            }
        }
    }

    fn remove_inner(
        &mut self,
        data_idx: DataIndex,
        ttl_evicted: TtlHeapIndex,
        lru_evicted: LruHeapIndex,
    ) {
        if let Some(&(ref key, _, ttl_idx, lru_idx)) = self.data.get(data_idx.data) {
            // fix map -> data
            let hash = self.hasher.hash_one(key);
            *self
                .map
                .get_mut(hash, |&idx| idx.data == self.data.len())
                .unwrap() = data_idx;

            // fix heap -> data
            let _old_data_idx = std::mem::replace(&mut self.ttl_heap[ttl_idx.ttl_heap].1, data_idx);
            debug_assert_eq!(_old_data_idx.data, self.data.len());
            let _old_data_idx = std::mem::replace(&mut self.lru_heap[lru_idx.lru_heap].1, data_idx);
            debug_assert_eq!(_old_data_idx.data, self.data.len());
        }

        let (old_ttl, _) = self.ttl_heap.swap_remove(ttl_evicted.ttl_heap);
        if let Some(&(current_ttl, _)) = self.ttl_heap.get(ttl_evicted.ttl_heap) {
            if old_ttl < current_ttl {
                self.ttl_downheap(current_ttl, ttl_evicted);
            } else {
                self.ttl_upheap(current_ttl, ttl_evicted);
            }
        }
        let (old_lru, _) = self.lru_heap.swap_remove(lru_evicted.lru_heap);
        if let Some(&(current_lru, _)) = self.lru_heap.get(lru_evicted.lru_heap) {
            if old_lru < current_lru {
                self.lru_downheap(current_lru, lru_evicted);
            } else {
                self.lru_upheap(current_lru, lru_evicted);
            }
        }
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        let hash = self.hasher.hash_one(key);

        let data_idx = self
            .map
            .remove_entry(hash, |&idx| key.equivalent(&self.data[idx.data].0))?;
        let (_, value, ttl_evicted, lru_evicted) = self.data.swap_remove(data_idx.data);

        self.remove_inner(data_idx, ttl_evicted, lru_evicted);
        Some(value)

        // let (_, value, ttl_evicted, lru_evicted) = self.data.swap_remove(data_idx.data);

        // if let Some(&(ref key, _, ttl_idx, lru_idx)) = self.data.get(data_idx.data) {
        //     // fix map -> data
        //     let hash = self.hasher.hash_one(key);
        //     *self
        //         .map
        //         .get_mut(hash, |&idx| idx.data == self.data.len())
        //         .unwrap() = data_idx;

        //     // fix heap -> data
        //     let _old_data_idx = std::mem::replace(&mut self.ttl_heap[ttl_idx.ttl_heap].1, data_idx);
        //     debug_assert_eq!(_old_data_idx.data, self.data.len());
        //     let _old_data_idx = std::mem::replace(&mut self.lru_heap[lru_idx.lru_heap].1, data_idx);
        //     debug_assert_eq!(_old_data_idx.data, self.data.len());
        // }

        // let (old_ttl, _) = self.ttl_heap.swap_remove(ttl_evicted.ttl_heap);
        // if let Some(&(current_ttl, _)) = self.ttl_heap.get(ttl_evicted.ttl_heap) {
        //     if old_ttl > current_ttl {
        //         self.ttl_downheap(current_ttl, ttl_evicted);
        //     } else {
        //         self.ttl_upheap(current_ttl, ttl_evicted);
        //     }
        // }
        // let (old_lru, _) = self.lru_heap.swap_remove(lru_evicted.lru_heap);
        // if let Some(&(current_lru, _)) = self.lru_heap.get(lru_evicted.lru_heap) {
        //     if old_lru > current_lru {
        //         self.lru_downheap(current_lru, lru_evicted);
        //     } else {
        //         self.lru_upheap(current_lru, lru_evicted);
        //     }
        // }

        // Some(value)
    }

    pub fn peek<Q>(&self, key: &Q) -> Option<(T, &V)>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        let hash = self.hasher.hash_one(key);
        let data_idx = *self
            .map
            .get(hash, |&idx| key.equivalent(&self.data[idx.data].0))?;
        let (_, ref value, ttl_idx, _) = self.data[data_idx.data];
        let &(ttl, _data_idx) = self.ttl_heap.get(ttl_idx.ttl_heap).unwrap();
        debug_assert_eq!(data_idx, _data_idx);
        Some((ttl, value))
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<(T, &mut V)>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        let hash = self.hasher.hash_one(key);
        let data_idx = *self
            .map
            .get(hash, |&idx| key.equivalent(&self.data[idx.data].0))?;

        let epoch = self.epoch;
        self.epoch += 1;

        let lru_idx = self.data[data_idx.data].3;
        self.lru_heap[lru_idx.lru_heap].0 = epoch;
        self.data[data_idx.data].3 = self.lru_downheap(epoch, lru_idx);

        let (_, ref mut value, ttl_idx, _) = self.data[data_idx.data];
        let &(ttl, _data_idx) = self.ttl_heap.get(ttl_idx.ttl_heap).unwrap();
        debug_assert_eq!(data_idx, _data_idx);
        Some((ttl, value))
    }

    /// Gets an [`InsertSlot`] into this table at the given hash.
    ///
    /// # Safety
    /// table must have spare capacity for 1 entry
    unsafe fn insert_slot_no_grow(&mut self, hash: u64) -> InsertSlot {
        let growth_left = self.map.capacity() - self.map.len();
        if 1 > growth_left {
            unsafe { std::hint::unreachable_unchecked() }
        }
        let slot = self.map.find_or_find_insert_slot(
            hash,
            // this entry is not equal to any other entry
            |_| false,
            // this table won't regrow
            |_| unreachable!(),
        );
        match slot {
            Ok(_) => unreachable!(),
            Err(slot) => slot,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroUsize;

    use crate::TtlMap;

    #[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Copy)]
    struct Instant(pub usize);

    const NOW: Instant = Instant(0);
    const LATER: Instant = Instant(1);
    const AFTER: Instant = Instant(2);

    #[test]
    fn can_expire() {
        let mut map = TtlMap::with_capacity(NonZeroUsize::new(4).unwrap());

        map.insert(NOW, "a", 1, AFTER);
        map.insert(NOW, "b", 2, LATER);
        map.insert(NOW, "c", 3, AFTER);
        map.insert(NOW, "d", 4, LATER);

        assert_eq!(map.len(), 4);

        assert_eq!(map.peek("a"), Some((AFTER, &1)));
        assert_eq!(map.peek("b"), Some((LATER, &2)));
        assert_eq!(map.peek("c"), Some((AFTER, &3)));
        assert_eq!(map.peek("d"), Some((LATER, &4)));

        map.insert(LATER, "e", 5, AFTER);
        assert_eq!(map.len(), 3);
        map.insert(LATER, "f", 6, AFTER);
        assert_eq!(map.len(), 4);

        assert_eq!(map.peek("a"), Some((AFTER, &1)));
        assert_eq!(map.peek("b"), None);
        assert_eq!(map.peek("c"), Some((AFTER, &3)));
        assert_eq!(map.peek("d"), None);
        assert_eq!(map.peek("e"), Some((AFTER, &5)));
        assert_eq!(map.peek("f"), Some((AFTER, &6)));
    }

    #[test]
    fn lru() {
        let mut map = TtlMap::with_capacity(NonZeroUsize::new(4).unwrap());

        map.insert(NOW, "a", 1, AFTER);
        map.insert(NOW, "b", 2, AFTER);
        map.insert(NOW, "c", 3, AFTER);
        map.insert(NOW, "d", 4, AFTER);

        assert_eq!(map.len(), 4);

        assert_eq!(map.get_mut("a"), Some((AFTER, &mut 1)));
        assert_eq!(map.get_mut("b"), Some((AFTER, &mut 2)));
        assert_eq!(map.get_mut("d"), Some((AFTER, &mut 4)));

        // peek won't update the recently-used state
        assert_eq!(map.peek("c"), Some((AFTER, &3)));

        map.insert(LATER, "e", 5, AFTER);
        assert_eq!(map.len(), 4);

        dbg!(&map);

        assert_eq!(map.peek("a"), Some((AFTER, &1)));
        assert_eq!(map.peek("b"), Some((AFTER, &2)));
        assert_eq!(map.peek("c"), None);
        assert_eq!(map.peek("d"), Some((AFTER, &4)));
        assert_eq!(map.peek("e"), Some((AFTER, &5)));
    }

    #[test]
    fn test_put_and_get() {
        let mut cache = TtlMap::with_capacity(NonZeroUsize::new(2).unwrap());
        cache.insert(NOW, 1, 10, LATER);
        cache.insert(NOW, 2, 20, LATER);
        assert_eq!(cache.get_mut(&1), Some((LATER, &mut 10)));
        assert_eq!(cache.get_mut(&2), Some((LATER, &mut 20)));
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_put_update() {
        let mut cache = TtlMap::with_capacity(NonZeroUsize::new(1).unwrap());
        cache.insert(NOW, "1", 10, LATER);
        cache.insert(NOW, "1", 19, LATER);
        assert_eq!(cache.get_mut("1"), Some((LATER, &mut 19)));
        assert_eq!(cache.len(), 1);
    }

    // #[test]
    // fn test_contains_key() {
    //     let mut cache = TtlMap::with_capacity(NonZeroUsize::new(1).unwrap());
    //     cache.insert(NOW, "1", 10, LATER);
    //     assert_eq!(cache.contains_key("1"), true);
    // }

    #[test]
    fn test_expire_lru() {
        let mut cache = TtlMap::with_capacity(NonZeroUsize::new(2).unwrap());
        cache.insert(NOW, "foo1", "bar1", LATER);
        cache.insert(NOW, "foo2", "bar2", LATER);
        cache.insert(NOW, "foo3", "bar3", LATER);
        assert!(cache.get_mut("foo1").is_none());
        cache.insert(NOW, "foo2", "bar2update", LATER);
        cache.insert(NOW, "foo4", "bar4", LATER);
        assert!(cache.get_mut("foo3").is_none());
    }

    #[test]
    fn test_pop() {
        let mut cache = TtlMap::with_capacity(NonZeroUsize::new(2).unwrap());
        cache.insert(NOW, 1, 10, LATER);
        cache.insert(NOW, 2, 20, LATER);
        assert_eq!(cache.len(), 2);
        let opt1 = cache.remove(&1);
        assert!(opt1.is_some());
        assert_eq!(opt1.unwrap(), 10);
        assert!(cache.get_mut(&1).is_none());
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_change_capacity() {
        let mut cache = TtlMap::with_capacity(NonZeroUsize::new(2).unwrap());
        assert_eq!(cache.capacity().get(), 2);
        cache.insert(NOW, 1, 10, LATER);
        cache.insert(NOW, 2, 20, LATER);
        cache.set_capacity(NonZeroUsize::new(1).unwrap());
        // why should we remove stuff from the cache eagerly????
        // assert!(cache.get_mut(&1).is_none());
        assert_eq!(cache.capacity().get(), 1);
    }

    #[test]
    fn test_remove() {
        let mut cache = TtlMap::with_capacity(NonZeroUsize::new(3).unwrap());
        cache.insert(NOW, 1, 10, LATER);
        cache.insert(NOW, 2, 20, LATER);
        cache.insert(NOW, 3, 30, LATER);
        cache.insert(NOW, 4, 40, LATER);
        cache.insert(NOW, 5, 50, LATER);
        cache.remove(&3);
        cache.remove(&4);
        assert!(cache.get_mut(&3).is_none());
        assert!(cache.get_mut(&4).is_none());
        cache.insert(NOW, 6, 60, LATER);
        cache.insert(NOW, 7, 70, LATER);
        cache.insert(NOW, 8, 80, LATER);
        assert!(cache.get_mut(&5).is_none());
        assert_eq!(cache.get_mut(&6), Some((LATER, &mut 60)));
        assert_eq!(cache.get_mut(&7), Some((LATER, &mut 70)));
        assert_eq!(cache.get_mut(&8), Some((LATER, &mut 80)));
    }

    #[test]
    fn test_clear() {
        let mut cache = TtlMap::with_capacity(NonZeroUsize::new(2).unwrap());
        cache.insert(NOW, 1, 10, LATER);
        cache.insert(NOW, 2, 20, LATER);
        cache.clear();
        assert!(cache.get_mut(&1).is_none());
        assert!(cache.get_mut(&2).is_none());
        assert!(cache.is_empty())
    }

    // #[test]
    // fn test_iter() {
    //     let mut cache = TtlMap::with_capacity(NonZeroUsize::new(3).unwrap());
    //     cache.insert(NOW, 1, 10, LATER);
    //     cache.insert(NOW, 2, 20, LATER);
    //     cache.insert(NOW, 3, 30, LATER);
    //     cache.insert(NOW, 4, 40, LATER);
    //     cache.insert(NOW, 5, 50, LATER);
    //     assert_eq!(
    //         cache.iter().collect::<Vec<_>>(),
    //         [(&3, &30), (&4, &40), (&5, &50)]
    //     );
    //     assert_eq!(
    //         cache.iter_mut().collect::<Vec<_>>(),
    //         [(&3, &mut 30), (&4, &mut 40), (&5, &mut 50)]
    //     );
    //     assert_eq!(
    //         cache.iter().rev().collect::<Vec<_>>(),
    //         [(&5, &50), (&4, &40), (&3, &30)]
    //     );
    //     assert_eq!(
    //         cache.iter_mut().rev().collect::<Vec<_>>(),
    //         [(&5, &mut 50), (&4, &mut 40), (&3, &mut 30)]
    //     );
    // }

    // #[test]
    // fn test_peek() {
    //     let mut cache = TtlMap::with_capacity(NonZeroUsize::new(6)).unwrap();
    //     cache.insert(NOW, 1, 10, LATER);
    //     cache.insert(NOW, 2, 20, LATER);
    //     cache.insert(NOW, 3, 30, LATER);
    //     cache.insert(NOW, 4, 40, LATER);
    //     cache.insert(NOW, 5, 50, LATER);
    //     cache.insert(NOW, 6, 60, LATER);

    //     assert_eq!(cache.remove_lru(), Some((1, 10)));
    //     assert_eq!(cache.peek(&2), Some(&20));
    //     assert_eq!(cache.remove_lru(), Some((2, 20)));
    //     assert_eq!(cache.peek_mut(&3), Some((LATER, &mut 30)));
    //     assert_eq!(cache.remove_lru(), Some((3, 30)));
    //     assert_eq!(cache.get(&4), Some(&40));
    //     assert_eq!(cache.remove_lru(), Some((5, 50)));
    // }

    // #[test]
    // fn test_entry() {
    //     let mut cache = TtlMap::with_capacity(NonZeroUsize::new(4).unwrap());

    //     cache.insert(NOW, 1, 10, LATER);
    //     cache.insert(NOW, 2, 20, LATER);
    //     cache.insert(NOW, 3, 30, LATER);
    //     cache.insert(NOW, 4, 40, LATER);
    //     cache.insert(NOW, 5, 50, LATER);
    //     cache.insert(NOW, 6, 60, LATER);

    //     assert_eq!(cache.len(), 4);

    //     cache.entry(7).or_insert(70);
    //     cache.entry(8).or_insert(80);
    //     cache.entry(9).or_insert(90);

    //     assert!(cache.len() <= 5);

    //     cache.raw_entry_mut().from_key(&10).or_insert(10, 100);
    //     cache.raw_entry_mut().from_key(&11).or_insert(11, 110);
    //     cache.raw_entry_mut().from_key(&12).or_insert(12, 120);

    //     assert!(cache.len() <= 5);
    // }
}
