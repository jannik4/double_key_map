mod ptr;

use self::ptr::Ptr;
use std::{
    collections::{hash_map::RandomState, HashMap},
    hash::{BuildHasher, Hash},
};

// Invariants to maintain:
// - data.len() == map1.len() == map2.len()
// - map1 contains all indices in data exactly once with the same key as in data
// - map2 contains all indices in data exactly once with the same key as in data

#[derive(Debug)]
pub struct DoubleKeyMap<K1, K2, V, S = RandomState> {
    data: Vec<(Ptr<K1>, Ptr<K2>, V)>,
    map1: HashMap<Ptr<K1>, usize, S>,
    map2: HashMap<Ptr<K2>, usize, S>,
}

impl<K1, K2, V> DoubleKeyMap<K1, K2, V, RandomState> {
    pub fn new() -> Self {
        Self { data: Vec::new(), map1: HashMap::new(), map2: HashMap::new() }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: Vec::with_capacity(capacity),
            map1: HashMap::with_capacity(capacity),
            map2: HashMap::with_capacity(capacity),
        }
    }
}

impl<K1, K2, V, S: Clone> DoubleKeyMap<K1, K2, V, S> {
    pub fn with_hasher(hash_builder: S) -> Self {
        Self {
            data: Vec::new(),
            map1: HashMap::with_hasher(hash_builder.clone()),
            map2: HashMap::with_hasher(hash_builder),
        }
    }

    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            data: Vec::with_capacity(capacity),
            map1: HashMap::with_capacity_and_hasher(capacity, hash_builder.clone()),
            map2: HashMap::with_capacity_and_hasher(capacity, hash_builder),
        }
    }
}

impl<K1, K2, V, S> DoubleKeyMap<K1, K2, V, S> {
    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn clear(&mut self) {
        self.map1.clear();
        self.map2.clear();
        for (k1, k2, v) in self.data.drain(..) {
            // SAFETY: We just cleared the maps, so the keys are no longer used elsewhere.
            unsafe {
                Ptr::drop(k1);
                Ptr::drop(k2);
                drop(v);
            }
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K1, &K2, &V)> {
        self.into_iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = (&K1, &K2, &mut V)> {
        self.into_iter()
    }

    pub fn keys1(&self) -> impl Iterator<Item = &K1> {
        self.map1.keys().map(|k| &**k)
    }

    pub fn keys2(&self) -> impl Iterator<Item = &K2> {
        self.map2.keys().map(|k| &**k)
    }

    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.data.iter().map(|(_, _, v)| v)
    }

    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.data.iter_mut().map(|(_, _, v)| v)
    }
}

impl<K1, K2, V, S: BuildHasher> DoubleKeyMap<K1, K2, V, S> {
    pub fn insert(&mut self, k1: K1, k2: K2, v: V)
    where
        K1: Hash + Eq,
        K2: Hash + Eq,
    {
        // Remove the old values
        self.remove1(&k1);
        self.remove2(&k2);

        // Create ptrs to the keys
        let k1 = Ptr::new(k1);
        let k2 = Ptr::new(k2);

        // Insert into data
        let idx = self.data.len();
        self.data.push((k1, k2, v));

        // Insert into the maps
        // These asserts are critical to protect against UB if the keys Eq/Hash impls are broken.
        assert!(self.map1.insert(k1, idx).is_none());
        assert!(self.map2.insert(k2, idx).is_none());
    }

    pub fn remove1(&mut self, key: &K1) -> Option<(K1, K2, V)>
    where
        K1: Hash + Eq,
        K2: Hash + Eq,
    {
        // Remove the element from the map
        let idx = self.map1.remove(key)?;

        // Swap the element to the end and remove it
        let (k1, k2, v) = self.data.swap_remove(idx);

        // Remove the element from the other map
        // This assert is critical to protect against UB if the keys Eq/Hash impls are broken.
        assert_eq!(self.map2.remove(&k2).unwrap(), idx);

        // Update the index in the maps of the element that was swapped in
        if idx < self.data.len() {
            let (k1, k2, _) = &self.data[idx];

            let map1_idx = self.map1.get_mut(k1).unwrap();
            // This assert is critical to protect against UB if the keys Eq/Hash impls are broken.
            assert_eq!(*map1_idx, self.data.len());
            *map1_idx = idx;

            let map2_idx = self.map2.get_mut(k2).unwrap();
            // This assert is critical to protect against UB if the keys Eq/Hash impls are broken.
            assert_eq!(*map2_idx, self.data.len());
            *map2_idx = idx;
        }

        // Safety: k1 and k2 are removed from data/map1/map2 and were never exposed
        // In more detail, each idx can at most be inserted once per map (see insert) and this
        // method removes exactly one idx from each map and asserts that the idx is the same.
        let (k1, k2) = unsafe { (*Ptr::into_owned(k1), *Ptr::into_owned(k2)) };

        Some((k1, k2, v))
    }

    pub fn remove2(&mut self, key: &K2) -> Option<(K1, K2, V)>
    where
        K1: Hash + Eq,
        K2: Hash + Eq,
    {
        // Remove the element from the map
        let idx = self.map2.remove(key)?;

        // Swap the element to the end and remove it
        let (k1, k2, v) = self.data.swap_remove(idx);

        // Remove the element from the other map
        // This assert is critical to protect against UB if the keys Eq/Hash impls are broken.
        assert_eq!(self.map1.remove(&k1).unwrap(), idx);

        // Update the index of the element that was swapped in
        if idx < self.data.len() {
            let (k1, k2, _) = &self.data[idx];

            let map1_idx = self.map1.get_mut(k1).unwrap();
            // This assert is critical to protect against UB if the keys Eq/Hash impls are broken.
            assert_eq!(*map1_idx, self.data.len());
            *map1_idx = idx;

            let map2_idx = self.map2.get_mut(k2).unwrap();
            // This assert is critical to protect against UB if the keys Eq/Hash impls are broken.
            assert_eq!(*map2_idx, self.data.len());
            *map2_idx = idx;
        }

        // Safety: k1 and k2 are removed from data/map1/map2 and were never exposed
        // In more detail, each idx can at most be inserted once per map (see insert) and this
        // method removes exactly one idx from each map and asserts that the idx is the same.
        let (k1, k2) = unsafe { (*Ptr::into_owned(k1), *Ptr::into_owned(k2)) };

        Some((k1, k2, v))
    }

    pub fn get1(&self, key: &K1) -> Option<(&K1, &K2, &V)>
    where
        K1: Hash + Eq,
    {
        let idx = *self.map1.get(key)?;
        let (k1, k2, v) = &self.data[idx];
        Some((&**k1, &**k2, v))
    }

    pub fn get2(&self, key: &K2) -> Option<(&K1, &K2, &V)>
    where
        K2: Hash + Eq,
    {
        let idx = *self.map2.get(key)?;
        let (k1, k2, v) = &self.data[idx];
        Some((&**k1, &**k2, v))
    }

    pub fn get1_mut(&mut self, key: &K1) -> Option<(&K1, &K2, &mut V)>
    where
        K1: Hash + Eq,
    {
        let idx = *self.map1.get(key)?;
        let (k1, k2, v) = &mut self.data[idx];
        Some((&**k1, &**k2, v))
    }

    pub fn get2_mut(&mut self, key: &K2) -> Option<(&K1, &K2, &mut V)>
    where
        K2: Hash + Eq,
    {
        let idx = *self.map2.get(key)?;
        let (k1, k2, v) = &mut self.data[idx];
        Some((&**k1, &**k2, v))
    }

    pub fn contains_key1(&self, key: &K1) -> bool
    where
        K1: Hash + Eq,
    {
        self.map1.contains_key(key)
    }

    pub fn contains_key2(&self, key: &K2) -> bool
    where
        K2: Hash + Eq,
    {
        self.map2.contains_key(key)
    }
}

impl<K1, K2, V, S: Clone + Default> Default for DoubleKeyMap<K1, K2, V, S> {
    fn default() -> Self {
        Self::with_hasher(Default::default())
    }
}

impl<K1, K2, V, S> Clone for DoubleKeyMap<K1, K2, V, S>
where
    K1: Hash + Eq + Clone,
    K2: Hash + Eq + Clone,
    V: Clone,
    S: Clone + Default + BuildHasher,
{
    fn clone(&self) -> Self {
        let data = self
            .data
            .iter()
            .map(|(k1, k2, v)| (Ptr::new((**k1).clone()), Ptr::new((**k2).clone()), v.clone()))
            .collect::<Vec<_>>();
        let map1 =
            data.iter().enumerate().map(|(i, (k1, _, _))| (*k1, i)).collect::<HashMap<_, _, S>>();
        let map2 =
            data.iter().enumerate().map(|(i, (_, k2, _))| (*k2, i)).collect::<HashMap<_, _, S>>();

        // This assert is critical to protect against UB if the keys Eq/Hash impls are broken.
        assert!(data.len() == map1.len() && data.len() == map2.len());

        Self { data, map1, map2 }
    }
}

impl<K1, K2, V, S> FromIterator<(K1, K2, V)> for DoubleKeyMap<K1, K2, V, S>
where
    K1: Hash + Eq,
    K2: Hash + Eq,
    S: Clone + Default + BuildHasher,
{
    fn from_iter<T: IntoIterator<Item = (K1, K2, V)>>(iter: T) -> Self {
        let mut map = Self::with_hasher(Default::default());
        for (k1, k2, v) in iter {
            map.insert(k1, k2, v);
        }
        map
    }
}

#[allow(clippy::type_complexity)]
pub struct Iter<'a, K1, K2, V> {
    inner: std::iter::Map<
        std::slice::Iter<'a, (Ptr<K1>, Ptr<K2>, V)>,
        fn(&(Ptr<K1>, Ptr<K2>, V)) -> (&K1, &K2, &V),
    >,
}

impl<'a, K1, K2, V> Iterator for Iter<'a, K1, K2, V> {
    type Item = (&'a K1, &'a K2, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<'a, K1, K2, V, S> IntoIterator for &'a DoubleKeyMap<K1, K2, V, S> {
    type Item = (&'a K1, &'a K2, &'a V);

    type IntoIter = Iter<'a, K1, K2, V>;

    fn into_iter(self) -> Self::IntoIter {
        Iter { inner: self.data.iter().map(|(k1, k2, v)| (&**k1, &**k2, v)) }
    }
}

#[allow(clippy::type_complexity)]
pub struct IterMut<'a, K1, K2, V> {
    inner: std::iter::Map<
        std::slice::IterMut<'a, (Ptr<K1>, Ptr<K2>, V)>,
        fn(&mut (Ptr<K1>, Ptr<K2>, V)) -> (&K1, &K2, &mut V),
    >,
}

impl<'a, K1, K2, V> Iterator for IterMut<'a, K1, K2, V> {
    type Item = (&'a K1, &'a K2, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<'a, K1, K2, V, S> IntoIterator for &'a mut DoubleKeyMap<K1, K2, V, S> {
    type Item = (&'a K1, &'a K2, &'a mut V);

    type IntoIter = IterMut<'a, K1, K2, V>;

    fn into_iter(self) -> Self::IntoIter {
        IterMut { inner: self.data.iter_mut().map(|(k1, k2, v)| (&**k1, &**k2, v)) }
    }
}

#[allow(clippy::type_complexity)]
pub struct IntoIter<K1, K2, V> {
    inner: std::iter::Map<
        std::vec::IntoIter<(Ptr<K1>, Ptr<K2>, V)>,
        fn((Ptr<K1>, Ptr<K2>, V)) -> (K1, K2, V),
    >,
}

impl<K1, K2, V> Iterator for IntoIter<K1, K2, V> {
    type Item = (K1, K2, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<K1, K2, V, S> IntoIterator for DoubleKeyMap<K1, K2, V, S> {
    type Item = (K1, K2, V);

    type IntoIter = IntoIter<K1, K2, V>;

    fn into_iter(self) -> Self::IntoIter {
        drop(self.map1);
        drop(self.map2);

        IntoIter {
            inner: self.data.into_iter().map(|(k1, k2, v)| {
                // SAFETY: We just dropped the maps, so the keys are no longer used elsewhere.
                unsafe { (*Ptr::into_owned(k1), *Ptr::into_owned(k2), v) }
            }),
        }
    }
}
