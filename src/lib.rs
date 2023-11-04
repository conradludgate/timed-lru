use std::{
    collections::hash_map::RandomState,
    fmt::Debug,
    hash::{BuildHasher, Hash},
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
struct HeapIndex {
    heap: usize,
}

pub struct TtlMap<K, V, T> {
    hasher: RandomState,
    // stored indices to heap, hashed by K
    map: RawTable<DataIndex>,

    data: Vec<(K, V, HeapIndex)>,

    // min heap by instant
    heap: Vec<(T, DataIndex)>,
    capacity: usize,
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
            .field("heap", &self.heap)
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

    pub fn with_capacity(capacity: usize) -> Self {
        TtlMap {
            hasher: RandomState::new(),
            map: RawTable::with_capacity(capacity),
            data: Vec::with_capacity(capacity),
            heap: Vec::with_capacity(capacity),
            capacity,
        }
    }

    pub fn len(&self) -> usize {
        self.heap.len()
    }

    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    pub fn is_full(&self) -> bool {
        self.len() == self.capacity
    }

    /// evicts all expired entries
    /// will re-position elements in the map
    fn evict(&mut self, now: T) {
        while self.evict1(now) {}
    }

    /// evicts a single expired entry from the map.
    /// will re-position elements in the map
    fn evict1(&mut self, now: T) -> bool {
        let Some(&(expires, _)) = self.heap.first() else {
            return false;
        };

        if expires > now {
            return false;
        }

        let heap_evicted = HeapIndex { heap: 0 };
        let (_, data_evicted) = self.heap.swap_remove(heap_evicted.heap);
        // fix data -> heap
        if let Some(&(_, data_idx)) = self.heap.get(heap_evicted.heap) {
            let _old_heap_idx = std::mem::replace(&mut self.data[data_idx.data].2, heap_evicted);
            debug_assert_eq!(_old_heap_idx.heap, self.heap.len());
        }

        let (key, _, _evicted) = self.data.swap_remove(data_evicted.data);
        debug_assert_eq!(_evicted.heap, 0);

        // remove data from map
        let hash = self.hasher.hash_one(&key);
        self.map
            .remove_entry(hash, |&idx| idx.data == data_evicted.data)
            .unwrap();

        if let Some(&(ref key, _, heap_idx)) = self.data.get(data_evicted.data) {
            // fix map -> data
            let hash = self.hasher.hash_one(key);
            *self
                .map
                .get_mut(hash, |&idx| idx.data == self.data.len())
                .unwrap() = data_evicted;

            // fix heap -> data
            let _old_data_idx = std::mem::replace(&mut self.heap[heap_idx.heap].1, data_evicted);
            debug_assert_eq!(_old_data_idx.data, self.data.len());
        }

        if self.heap.is_empty() {
            return false;
        }

        // push down the entry we swapped
        let heap_idx = self.downheap(self.heap[0].0, HeapIndex { heap: 0 });

        // fix data -> heap
        let data_idx = self.heap[heap_idx.heap].1;
        self.data[data_idx.data].2 = heap_idx;

        true
    }

    /// move a new element that has a larger TTL down the heap
    /// will not re-position elements in the map
    fn downheap(&mut self, expires: T, mut i: HeapIndex) -> HeapIndex {
        loop {
            let left = HeapIndex {
                heap: 2 * i.heap + 1,
            };
            let right = HeapIndex {
                heap: 2 * i.heap + 2,
            };

            let mut largest = i;
            if left.heap < self.heap.len() && self.heap[left.heap].0 < expires {
                largest = left
            }
            if right.heap < self.heap.len() && self.heap[right.heap].0 < expires {
                largest = right
            }

            if largest == i {
                break i;
            }

            let data_idx = self.heap[largest.heap].1;
            self.data[data_idx.data].2 = i;

            self.heap.swap(i.heap, largest.heap);
            i = largest;
        }
    }

    /// move a new element that has a shorter TTL up the heap.
    /// will not re-position elements in the map
    fn upheap(&mut self, expires: T, mut i: HeapIndex) -> HeapIndex {
        while i.heap > 0 {
            let parent = HeapIndex {
                heap: (i.heap - 1) / 2,
            };

            // check if we need to continue
            if expires > self.heap[parent.heap].0 {
                break;
            }

            let data_idx = self.heap[parent.heap].1;
            self.data[data_idx.data].2 = i;

            self.heap.swap(i.heap, parent.heap);
            i = parent;
        }
        i
    }

    pub fn insert(&mut self, now: T, key: K, value: V, expires: T) -> Option<V> {
        let hash = self.hasher.hash_one(&key);

        let slot = if self.heap.len() >= self.capacity {
            match self.map.find(hash, |&idx| self.data[idx.data].0 == key) {
                // we are at capacity but we will replace an existing entry
                Some(bucket) => Ok(bucket),
                // we will overflow capacity. evict
                None => {
                    self.evict(now);
                    // ideally there would be a function that only find and return an insert slot for a given hash.
                    // we already know the element isn't here and (once I implement LRU), we know there's spare capacity.
                    // TODO: could probably force it to compile that way by making the `eq` always return false and the hasher unreachable_unchecked().
                    // see insert_slot_no_grow below
                    self.map.find_or_find_insert_slot(
                        hash,
                        |&idx| self.data[idx.data].0 == key,
                        |&idx| self.hasher.hash_one(&self.data[idx.data].0),
                    )
                }
            }
        } else {
            self.map.find_or_find_insert_slot(
                hash,
                |&idx| self.data[idx.data].0 == key,
                |&idx| self.hasher.hash_one(&self.data[idx.data].0),
            )
        };

        match slot {
            Ok(bucket) => {
                // SAFETY: we haven't updated the hashtable so this bucket still points to the correct place
                let data_idx = unsafe { *bucket.as_ref() };

                self.data[data_idx.data].0 = key;
                let old_value = std::mem::replace(&mut self.data[data_idx.data].1, value);
                let heap_idx = self.data[data_idx.data].2;
                let would_expire = self.heap[heap_idx.heap].0;

                let heap_idx = if expires >= would_expire {
                    self.downheap(expires, heap_idx)
                } else {
                    self.upheap(expires, heap_idx)
                };

                // fix data -> heap
                let data_idx = self.heap[heap_idx.heap].1;
                self.data[data_idx.data].2 = heap_idx;

                Some(old_value)
            }
            Err(slot) => {
                let heap_idx = HeapIndex {
                    heap: self.heap.len(),
                };
                let data_idx = DataIndex {
                    data: self.data.len(),
                };

                // TODO: push_within_capacity?
                self.heap.push((expires, data_idx));
                self.data.push((key, value, heap_idx));

                // SAFETY: we haven't updated the hashtable positions so this slot still points to the correct place
                unsafe { self.map.insert_in_slot(hash, slot, data_idx) };

                let heap_idx = self.upheap(expires, heap_idx);

                // fix data -> heap
                let data_idx = self.heap[heap_idx.heap].1;
                self.data[data_idx.data].2 = heap_idx;

                None
            }
        }
    }

    pub fn get<Q>(&mut self, key: &Q) -> Option<(T, &V)>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        let hash = self.hasher.hash_one(key);
        let data_idx = *self
            .map
            .get(hash, |&idx| key.equivalent(&self.data[idx.data].0))?;
        let &(_, ref value, heap_idx) = self.data.get(data_idx.data).unwrap();
        let &(ttl, _data_idx) = self.heap.get(heap_idx.heap).unwrap();
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
    use crate::TtlMap;

    #[test]
    fn can_expire() {
        let mut map = TtlMap::with_capacity(4);

        let now = 0;
        let later = 1;
        let after = 2;

        map.insert(now, "a", 1, after);
        map.insert(now, "b", 2, later);
        map.insert(now, "c", 3, after);
        map.insert(now, "d", 4, later);

        assert_eq!(map.len(), 4);

        assert_eq!(map.get("a"), Some((after, &1)));
        assert_eq!(map.get("b"), Some((later, &2)));
        assert_eq!(map.get("c"), Some((after, &3)));
        assert_eq!(map.get("d"), Some((later, &4)));

        map.insert(later, "e", 5, after);
        assert_eq!(map.len(), 3);
        map.insert(later, "f", 6, after);
        assert_eq!(map.len(), 4);

        assert_eq!(map.get("a"), Some((after, &1)));
        assert_eq!(map.get("b"), None);
        assert_eq!(map.get("c"), Some((after, &3)));
        assert_eq!(map.get("d"), None);
        assert_eq!(map.get("e"), Some((after, &5)));
        assert_eq!(map.get("f"), Some((after, &6)));
    }
}
