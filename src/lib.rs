use std::{
    collections::hash_map::RandomState,
    hash::{BuildHasher, Hash, Hasher},
    time::Instant,
};

use hashbrown::{
    raw::{InsertSlot, RawTable},
    Equivalent,
};

// struct TtlMap<K, V> {
//     hasher: RandomState,
//     // stored indices to data, hashed by K
//     map: RawTable<usize>,
//     // key, value, heap_position
//     data: Vec<(K, V, usize)>,
//     // min heap by instant, usize in the index into the data
//     heap: Vec<(Instant, usize)>,
// }

// impl<K: Hash, V> TtlMap<K, V> {
//     // find the entry that is next to expire
//     fn peek_front(&self, now: Instant) -> Option<usize> {
//         let (time, space) = *self.heap.first()?;
//         (time < now).then_some(space)
//     }

//     // evict expired entries
//     fn evict(&mut self, now: Instant) {
//         while let Some(expired) = self.peek_front(now) {
//             let _ = self.heap.swap_remove(0);

//             // remove data from map
//             {
//                 let (key, _, _expired) = self.data.swap_remove(expired);
//                 debug_assert_eq!(expired, _expired);

//                 let hash = {
//                     let mut hasher = self.hasher.build_hasher();
//                     key.hash(&mut hasher);
//                     hasher.finish()
//                 };
//                 self.map.remove_entry(hash, |&idx| idx == expired).unwrap();
//             }

//             // update data -> heap relationship
//             if let Some(&(_, x)) = self.heap.first() {
//                 self.data[x].2 = 0;
//             }

//             // update heap -> data relationship
//             if let Some(&(ref k, _, heap_pos)) = self.data.get(expired) {
//                 let hash = {
//                     let mut hasher = self.hasher.build_hasher();
//                     k.hash(&mut hasher);
//                     hasher.finish()
//                 };
//                 // find the entry that was pointing to the end we swapped, then update it
//                 *self
//                     .map
//                     .get_mut(hash, |&idx| idx == self.data.len())
//                     .unwrap() = expired;

//                 // make sure the corresponding heap entry points to the right place
//                 debug_assert_eq!(self.heap[heap_pos].1, self.data.len());
//                 self.heap[heap_pos].1 = expired;
//             }

//             //
//         }
//     }
// }

pub struct TtlMap2<K, V, T> {
    hasher: RandomState,
    // stored indices to heap, hashed by K
    map: RawTable<usize>,
    // min heap by instant
    heap: Vec<(T, K, V)>,
    capacity: usize,
}

impl<K: Hash + Eq, V, T: Ord + Copy> TtlMap2<K, V, T> {
    // // find the entry that is next to expire
    // fn peek_front(&self, now: Instant) -> Option<usize> {
    //     let (time, space) = *self.heap.first()?;
    //     (time < now).then_some(space)
    // }

    pub fn with_capacity(capacity: usize) -> Self {
        TtlMap2 {
            hasher: RandomState::new(),
            map: RawTable::with_capacity(capacity),
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
        let Some(&(expires, _, _)) = self.heap.first() else {
            return false;
        };

        if expires > now {
            return false;
        }

        let (_, key, _) = self.heap.swap_remove(0);

        // remove data from map
        let hash = self.hasher.hash_one(&key);
        self.map.remove_entry(hash, |&idx| idx == 0).unwrap();

        if self.heap.is_empty() {
            return false;
        }

        // push down the entry we swapped
        let i = self.downheap(self.heap[0].0, 0);

        // find the entry that was pointing to the end we swapped, then update it
        let hash = self.hasher.hash_one(&self.heap[i].1);
        *self
            .map
            .get_mut(hash, |&idx| idx == self.heap.len())
            .unwrap() = i;

        true
    }

    /// move a new element that has a larger TTL down the heap
    /// will not re-position elements in the map
    fn downheap(&mut self, expires: T, mut i: usize) -> usize {
        loop {
            let left = 2 * (i + 1) - 1;
            let right = 2 * (i + 1) + 1 - 1;

            let mut largest = i;
            if left < self.heap.len() && self.heap[left].0 < expires {
                largest = left
            }
            if right < self.heap.len() && self.heap[right].0 < expires {
                largest = right
            }

            if largest == i {
                break i;
            }

            let hash = self.hasher.hash_one(&self.heap[largest].1);
            *self.map.get_mut(hash, |&idx| idx == largest).unwrap() = i;
            self.heap.swap(i, largest);

            i = largest;
        }
    }

    /// move a new element that has a shorter TTL up the heap.
    /// will not re-position elements in the map
    fn upheap(&mut self, expires: T, mut i: usize) -> usize {
        while i > 0 {
            let parent = (i - 1) / 2;

            // check if we need to continue
            if expires > self.heap[parent].0 {
                break;
            }

            let hash = self.hasher.hash_one(&self.heap[parent].1);
            *self.map.get_mut(hash, |&idx| idx == parent).unwrap() = i;
            self.heap.swap(parent, i);

            i = parent;
        }
        i
    }

    pub fn insert(&mut self, now: T, key: K, value: V, expires: T) -> Option<V> {
        let hash = self.hasher.hash_one(&key);

        let slot = if self.heap.len() >= self.capacity {
            match self.map.find(hash, |&idx| self.heap[idx].1 == key) {
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
                        |&idx| self.heap[idx].1 == key,
                        |&idx| self.hasher.hash_one(&self.heap[idx].1),
                    )
                }
            }
        } else {
            self.map.find_or_find_insert_slot(
                hash,
                |&idx| self.heap[idx].1 == key,
                |&idx| self.hasher.hash_one(&self.heap[idx].1),
            )
        };

        match slot {
            Ok(bucket) => {
                // SAFETY: we haven't updated the hashtable so this bucket still points to the correct place
                let (i, slot) = unsafe { self.map.remove(bucket) };
                let (would_expire, _key, value) =
                    std::mem::replace(&mut self.heap[i], (expires, key, value));

                if expires >= would_expire {
                    let i = self.downheap(expires, i);

                    // SAFETY: we haven't updated the hashtable positions so this slot still points to the correct place
                    unsafe { self.map.insert_in_slot(hash, slot, i) };
                    Some(value)
                } else {
                    let i = self.upheap(expires, i);

                    // SAFETY: we haven't updated the hashtable positions so this slot still points to the correct place
                    unsafe { self.map.insert_in_slot(hash, slot, i) };
                    Some(value)
                }
            }
            Err(slot) => {
                let i = self.heap.len();
                // TODO: push_within_capacity?
                self.heap.push((expires, key, value));
                let i = self.upheap(expires, i);

                // SAFETY: we haven't updated the hashtable positions so this slot still points to the correct place
                unsafe { self.map.insert_in_slot(hash, slot, i) };
                None
            }
        }
    }

    pub fn get<Q>(&mut self, key: &Q) -> Option<(T, &V)>
    where
        Q: Hash + Equivalent<K> + ?Sized,
    {
        let hash = self.hasher.hash_one(key);
        let index = self
            .map
            .get(hash, |&idx| key.equivalent(&self.heap[idx].1))?;
        let &(ttl, _, ref value) = self.heap.get(*index).unwrap();
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
    use crate::TtlMap2;

    #[test]
    fn can_expire() {
        let mut map = TtlMap2::with_capacity(4);

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
