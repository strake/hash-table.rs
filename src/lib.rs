#![no_std]

extern crate siphasher as sip;

#[cfg(test)] extern crate quickcheck;
#[cfg(test)] #[macro_use]
             extern crate quickcheck_macros;
#[cfg(test)] #[macro_use]
             extern crate std;

use core::borrow::Borrow;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ops::{Index, IndexMut, RangeFull};
use core::{mem, ptr};
use core::mem::MaybeUninit as Slot;

#[derive(Clone, Default)]
pub struct DefaultHasher(::sip::sip::SipHasher);

impl Hasher for DefaultHasher {
    #[inline] fn finish(&self) -> u64 { self.0.finish() }
    #[inline] fn write(&mut self, bs: &[u8]) { self.0.write(bs) }
}

pub struct HashTable<K: Eq + Hash, T,
                     Hs: IndexMut<usize, Output = usize> + Index<RangeFull, Output = [usize]>,
                     Es: IndexMut<usize, Output = Slot<(K, T)>>, H: Clone + Hasher = DefaultHasher> {
    hashes: Hs,
    elems : Es,
    free_n: usize,
    hasher: H,
}

#[inline]
fn log2(n: usize) -> u32 { 0usize.count_zeros() - n.leading_zeros() - 1 }

impl<K: Eq + Hash, T, Hs: IndexMut<usize, Output = usize> + Index<RangeFull, Output = [usize]>,
     Es: IndexMut<usize, Output = Slot<(K, T)>>, H: Clone + Hasher> HashTable<K, T, Hs, Es, H> {
    #[inline]
    pub fn from_parts(mut hashes: Hs, elems: Es, hasher: H) -> Self {
        #[allow(clippy::needless_range_loop)]
        for k in 0..hashes[..].len() { hashes[k] = 0; }
        let free_n = 1 << log2(hashes[..].len());
        HashTable { hashes, elems, hasher, free_n }
    }

    fn log_cap(&self) -> u32 { log2(self.hashes[..].len()) }

    fn hash<Q: ?Sized>(&self, k: &Q) -> usize where Q: Hash {
        let mut h = self.hasher.clone();
        k.hash(&mut h);
        (h.finish() as usize | hash_flag) & !dead_flag
    }

    fn find_ix<Q: ?Sized>(&self, k: &Q) -> Option<usize> where K: Borrow<Q>, Q: Eq + Hash {
        debug_assert!(self.free_n >= 1);
        let wrap_mask = (1 << self.log_cap()) - 1;
        let h = self.hash(k);
        let mut i = h & wrap_mask;
        let mut psl = 0;
        loop {
            if self.hashes[i] == 0 || psl > compute_psl(&self.hashes[..], i) { return None };
            if self.hashes[i] == h && unsafe { self.elems[i].assume_init_ref().0.borrow() == k } { return Some(i); }
            i = (i+1)&wrap_mask;
            debug_assert_ne!(h & wrap_mask, i);
            psl += 1;
        }
    }

    #[inline]
    pub fn find_with_ix<Q: ?Sized>(&self, k: &Q) -> Option<(usize, &K, &T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.find_ix(k).map(move |i| unsafe { (i, &self.elems[i].assume_init_ref().0, &self.elems[i].assume_init_ref().1) })
    }

    #[inline]
    pub fn find_mut_with_ix<Q: ?Sized>(&mut self, k: &Q) -> Option<(usize, &K, &mut T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.find_ix(k).map(move |i| unsafe { let &mut (ref k, ref mut v) = self.elems[i].assume_init_mut(); (i, k, v) })
    }

    #[inline]
    pub fn find<Q: ?Sized>(&self, k: &Q) -> Option<(&K, &T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.find_with_ix(k).map(|(_, k, x)| (k, x))
    }

    #[inline]
    pub fn find_mut<Q: ?Sized>(&mut self, k: &Q) -> Option<(&K, &mut T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.find_mut_with_ix(k).map(|(_, k, x)| (k, x))
    }

    #[inline]
    pub fn insert_with<F: FnOnce(Option<T>) -> T>(&mut self, k: K, f: F) -> Result<(usize, &K, &mut T), (K, F)> {
        if 1 >= self.free_n { return Err((k, f)); }
        self.free_n -= 1;

        let cap = 1 << self.log_cap();
        let mut h = self.hash(&k);
        let mut i = h&(cap-1);
        let mut psl = 0;
        loop { unsafe {
            if self.hashes[i] == 0 {
                self.hashes[i] = h;
                ptr::write(self.elems[i].assume_init_mut(), (k, f(None)));
                let &mut (ref k, ref mut v) = self.elems[i].assume_init_mut();
                return Ok((i, k, v))
            }

            if self.hashes[i] == h && self.elems[i].assume_init_ref().0 == k {
                self.hashes[i] |=  dead_flag;
                let x = ptr::read(&self.elems[i].assume_init_ref().1);
                ptr::write(&mut self.elems[i].assume_init_mut().1, f(Some(x)));
                self.hashes[i] &= !dead_flag;
                let &mut (ref k, ref mut v) = self.elems[i].assume_init_mut();
                return Ok((i, k, v))
            }

            if psl > compute_psl(&self.hashes[..], i) {
                let mut e = (k, f(None));
                loop {
                    mem::swap(&mut h, &mut self.hashes[i]);
                    mem::swap(&mut e, self.elems[i].assume_init_mut());
                    if h == 0 || is_dead(h) {
                        mem::forget(e);
                        let &mut (ref k, ref mut v) = self.elems[i].assume_init_mut();
                        return Ok((i, k, v));
                    };
                    i = (i+1)&(cap-1);
                }
            }

            i = (i+1)&(cap-1);
            debug_assert_ne!(h&(cap-1), i);
            psl += 1;
        } }
    }

    #[inline]
    pub fn insert_with_ix(&mut self, k: K, x: T) -> Result<(usize, Option<T>), (K, T)> {
        let mut opt_y = None;
        self.insert_with(k, |opt_x| { opt_y = opt_x; x })
            .map_err(|(k, f)| (k, f(None))).map(|(k, _, _)| (k, opt_y))
    }

    #[inline]
    pub fn insert(&mut self, k: K, x: T) -> Result<Option<T>, (K, T)> {
        self.insert_with_ix(k, x).map(|(_, opt_y)| opt_y)
    }

    #[inline]
    pub fn delete<Q: ?Sized>(&mut self, k: &Q) -> Option<T> where K: Borrow<Q>, Q: Eq + Hash {
        self.find_ix(k).map(move |i| unsafe {
            self.free_n += 1;
            debug_assert!(1 << self.log_cap() >= self.free_n);
            let (_, x) = ptr::read(self.elems[i].assume_init_ref());
            self.hashes[i] |= dead_flag;
            x
        })
    }

    #[inline]
    pub fn drain(&mut self) -> Drain<K, T> {
        DrainFilter {
            φ: PhantomData,
            hash_ptr: &mut self.hashes[0],
            elms_ptr: &mut self.elems[0] as *mut Slot<_> as *mut _,
            hash_end: (&mut self.hashes[0] as *mut usize).wrapping_add(self.hashes[..].len()),
            f: |_, _| true,
        }
    }

    #[inline]
    pub fn drain_filter<F: FnMut(&K, &mut T) -> bool>(&mut self, f: F) -> DrainFilter<K, T, F> {
        DrainFilter {
            φ: PhantomData,
            hash_ptr: &mut self.hashes[0],
            elms_ptr: &mut self.elems[0] as *mut Slot<_> as *mut _,
            hash_end: (&mut self.hashes[0] as *mut usize).wrapping_add(self.hashes[..].len()),
            f,
        }
    }

    #[inline]
    pub fn iter_with_ix(&self) -> IterWithIx<K, T> {
        IterWithIx {
            φ: PhantomData,
            hash_ptr: &self.hashes[0],
            elms_ptr: &self.elems[0] as *const Slot<_> as *const _,
            hash_top: &self.hashes[0],
            hash_end: self.hashes[..].as_ptr().wrapping_add(self.hashes[..].len()),
        }
    }

    #[inline]
    pub fn iter_mut_with_ix(&mut self) -> IterMutWithIx<K, T> {
        IterMutWithIx {
            φ: PhantomData,
            hash_ptr: &self.hashes[0],
            elms_ptr: &mut self.elems[0] as *mut Slot<_> as *mut _,
            hash_top: &self.hashes[0],
            hash_end: self.hashes[..].as_ptr().wrapping_add(self.hashes[..].len()),
        }
    }

    #[inline]
    pub fn hasher(&self) -> &H { &self.hasher }
}

#[derive(Clone, Copy)]
pub struct IterWithIx<'a, K, T> {
    φ: PhantomData<&'a ()>,
    hash_ptr: *const usize,
    elms_ptr: *const (K, T),
    hash_top: *const usize,
    hash_end: *const usize,
}

impl<'a, K: 'a, T: 'a> Iterator for IterWithIx<'a, K, T> {
    type Item = (usize, &'a K, &'a T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut r = None;
        while r.is_none() && self.hash_ptr != self.hash_end { unsafe {
            if 0 != ptr::read(self.hash_ptr) { r = Some((ptr_diff(self.hash_ptr, self.hash_top),
                                                         &(*self.elms_ptr).0,
                                                         &(*self.elms_ptr).1)); }
            self.hash_ptr = self.hash_ptr.wrapping_offset(1);
            self.elms_ptr = self.elms_ptr.offset(1);
        } }
        r
    }
}

unsafe impl<'a, K: Sync, T: Sync> Send for IterWithIx<'a, K, T> {}
unsafe impl<'a, K: Sync, T: Sync> Sync for IterWithIx<'a, K, T> {}

pub struct IterMutWithIx<'a, K, T> {
    φ: PhantomData<&'a mut ()>,
    hash_ptr: *const usize,
    elms_ptr: *mut (K, T),
    hash_top: *const usize,
    hash_end: *const usize,
}

unsafe impl<'a, K: Sync, T: Send> Send for IterMutWithIx<'a, K, T> {}
unsafe impl<'a, K: Sync, T: Sync> Sync for IterMutWithIx<'a, K, T> {}

impl<'a, K: 'a, T: 'a> Iterator for IterMutWithIx<'a, K, T> {
    type Item = (usize, &'a K, &'a mut T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut r = None;
        while r.is_none() && self.hash_ptr != self.hash_end { unsafe {
            if 0 != ptr::read(self.hash_ptr) { r = Some((ptr_diff(self.hash_ptr, self.hash_top),
                                                         &    (*self.elms_ptr).0,
                                                         &mut (*self.elms_ptr).1)); }
            self.hash_ptr = self.hash_ptr.wrapping_offset(1);
            self.elms_ptr = self.elms_ptr.offset(1);
        } }
        r
    }
}

pub type Drain<'a, K, T> = DrainFilter<'a, K, T, fn(&K, &mut T) -> bool>;

pub struct DrainFilter<'a, K, T, F: FnMut(&K, &mut T) -> bool> {
    φ: PhantomData<&'a mut ()>,
    hash_ptr: *mut usize,
    elms_ptr: *mut (K, T),
    hash_end: *mut usize,
    f: F
}

unsafe impl<'a, K: Sync, T: Send, F: FnMut(&K, &mut T) -> bool + Send> Send for DrainFilter<'a, K, T, F> {}
unsafe impl<'a, K: Sync, T: Sync, F: FnMut(&K, &mut T) -> bool + Sync> Sync for DrainFilter<'a, K, T, F> {}

impl<'a, K, T, F: FnMut(&K, &mut T) -> bool> Iterator for DrainFilter<'a, K, T, F> {
    type Item = (K, T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut r = None;
        while r.is_none() && self.hash_ptr != self.hash_end { unsafe {
            if 0 != *self.hash_ptr {
                let (ref k, ref mut v) = &mut *self.elms_ptr;
                if (self.f)(k, v) {
                    *self.hash_ptr = 0;
                    r = Some(ptr::read(self.elms_ptr));
                }
            }
            self.hash_ptr = self.hash_ptr.wrapping_offset(1);
            self.elms_ptr = self.elms_ptr.offset(1);
        } }
        r
    }
}

impl<'a, K, T, F: FnMut(&K, &mut T) -> bool> Drop for DrainFilter<'a, K, T, F> {
    #[inline]
    fn drop(&mut self) { for _ in self {} }
}

#[inline] fn compute_psl(hs: &[usize], i: usize) -> usize { usize::wrapping_sub(i, hs[i])&(hs.len()-1) }

#[inline] fn is_dead(h: usize) -> bool { 0 != h & dead_flag }

const dead_flag: usize = !(!0>>1);
const hash_flag: usize = dead_flag>>1;

impl<K: Eq + Hash, T,
     Hs: IndexMut<usize, Output = usize> + Index<RangeFull, Output = [usize]>,
     Es: IndexMut<usize, Output = Slot<(K, T)>>, H: Clone + Hasher> Drop for HashTable<K, T, Hs, Es, H> {
    #[inline] fn drop(&mut self) { unsafe {
        for i in 0..self.hashes[..].len() {
            if self.hashes[i] != 0 && !is_dead(self.hashes[i]) { ptr::drop_in_place(self.elems[i].assume_init_mut()); }
        }
    } }
}

#[inline] pub fn ptr_diff<T>(p: *const T, q: *const T) -> usize {
    use ::core::num::Wrapping as w;
    (w(p as usize) - w(q as usize)).0/mem::size_of::<T>()
}

#[cfg(test)] mod tests {
    use quickcheck::{ Arbitrary, Gen };
    use std::hash::*;
    use std::vec::Vec;

    use super::*;

    fn nub_by_0<S: Ord, T>(v: &mut Vec<(S, T)>) {
        // Only last element of test input vector with each key is kept in table, so we must delete the others.
        // We can not merely sort by reverse comparison rather than sort and reverse as we rely on stability.
        v.sort_by(|&(ref i, _), &(ref j, _)| Ord::cmp(i, j));
        v.reverse();
        let mut i = 1;
        while i < v.len() {
            while i < v.len() && v[i-1].0 == v[i].0 { v.remove(i); }
            i += 1;
        }
    }

    fn mk_ht<K: Eq + Hash, T, H: Clone + Hasher>(cap: usize, h: H) -> HashTable<K, T, Vec<usize>, Vec<Slot<(K, T)>>, H> {
        let mut es = Vec::with_capacity(cap);
        unsafe { es.set_len(cap) };
        HashTable::from_parts(vec![0; cap], es, h)
    }

    #[derive(Clone)]
    struct XorBytesHasher(u64);
    impl Hasher for XorBytesHasher {
        fn finish(&self) -> u64 { match self { &XorBytesHasher(h) => h } }
        fn write(&mut self, bs: &[u8]) {
            for &b in bs { self.0 ^= b as u64; }
        }
    }

    #[derive(Clone)]
    struct NullHasher;
    impl Hasher for NullHasher {
        fn finish(&self) -> u64 { 0 }
        fn write(&mut self, _: &[u8]) {}
    }

    // ¬([_; 0x100]: Copy + Clone). Grr. *irritation*
    #[derive(Copy, Clone, Debug)]
    struct ArrayOf0x100<T: Copy>([[T; 0x10]; 0x10]);
    impl<T: Arbitrary + Copy> Arbitrary for ArrayOf0x100<T> {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            unsafe {
                let mut a: [[T; 0x10]; 0x10] = mem::uninitialized();
                for i in 0..0x10 { for j in 0..0x10 { ptr::write(&mut a[i][j], T::arbitrary(g)); } }
                ArrayOf0x100(a)
            }
        }
    }

    #[derive(Clone)]
    struct ArrayOf0x100Hasher([[u64; 0x10]; 0x10], u64);
    impl Hasher for ArrayOf0x100Hasher {
        fn finish(&self) -> u64 { match self { &ArrayOf0x100Hasher(_, h) => h } }
        fn write(&mut self, bs: &[u8]) {
            for &b in bs { self.1 ^= self.0[b as usize >> 4][b as usize & 0x0F]; }
        }
    }

    #[quickcheck] fn insertion_sans_collision(mut v: Vec<u64>) -> bool {
        v.truncate(0x100);
        let log_cap = (v.len() + 1).next_power_of_two().trailing_zeros();
        let mut t = mk_ht::<u8, u64, _>(1 << log_cap, XorBytesHasher(0));
        for (k, &x) in v.iter().enumerate() { t.insert(k as u8, x).unwrap(); }
        v.iter().enumerate().all(|(k, x)| t.find(&(k as u8)) == Some((&(k as u8), &x)))
    }

    #[quickcheck] fn insertion_with_collision(mut v: Vec<(u8, u64)>) -> bool {
        let log_cap = (v.len() + 1).next_power_of_two().trailing_zeros();
        let mut t = mk_ht::<u8, u64, _>(1 << log_cap, NullHasher);
        for (k, x) in v.clone() { t.insert(k, x).unwrap(); }

        nub_by_0(&mut v);
        v.iter().all(|&(k, x)| t.find(&k) == Some((&k, &x)))
    }

    #[quickcheck] fn insertion_with_random_hash(a: ArrayOf0x100<u64>, mut v: Vec<(u8, u64)>) -> bool {
        let ArrayOf0x100(a) = a;

        let log_cap = (v.len() + 1).next_power_of_two().trailing_zeros();
        let mut t = mk_ht::<u8, u64, ArrayOf0x100Hasher>(1 << log_cap, ArrayOf0x100Hasher(a, 0));
        for (k, x) in v.clone() { t.insert(k, x).unwrap(); }

        nub_by_0(&mut v);
        v.iter().all(|&(k, x)| t.find(&k) == Some((&k, &x)))
    }

    #[quickcheck] fn deletion_sans_collision(mut v: Vec<u64>) -> bool {
        v.truncate(0x100);
        let log_cap = (v.len() + 1).next_power_of_two().trailing_zeros();
        let mut t = mk_ht::<u8, u64, _>(1 << log_cap, XorBytesHasher(0));
        for (k, &x) in v.iter().enumerate() { t.insert(k as u8, x).unwrap(); }
        v.iter().enumerate().all(|(k, &x)| t.find(&(k as u8)) == Some((&(k as u8), &x)) && t.delete(&(k as u8)) == Some(x) && t.find(&(k as u8)) == None)
    }

    #[quickcheck] fn deletion_with_collision(mut v: Vec<(u8, u64)>) -> bool {
        v.truncate(8);
        let log_cap = (v.len() + 1).next_power_of_two().trailing_zeros();
        let mut t = mk_ht::<u8, u64, _>(1 << log_cap, NullHasher);
        for (k, x) in v.clone() { t.insert(k, x).unwrap(); }

        nub_by_0(&mut v);
        v.iter().all(|&(k, x)| t.find(&(k as u8)) == Some((&k, &x)) && t.delete(&k) == Some(x) && t.find(&k) == None)
    }

    #[quickcheck] fn deletion_with_random_hash(a: ArrayOf0x100<u64>, mut v: Vec<(u8, u64)>) -> bool {
        let ArrayOf0x100(a) = a;

        let log_cap = (v.len() + 1).next_power_of_two().trailing_zeros();
        let mut t = mk_ht::<u8, u64, _>(1 << log_cap, ArrayOf0x100Hasher(a, 0));
        for (k, x) in v.clone() { t.insert(k, x).unwrap(); }

        nub_by_0(&mut v);
        v.iter().all(|&(k, x)| t.find(&k) == Some((&k, &x)) && t.delete(&k) == Some(x) && t.find(&k) == None)
    }

    #[quickcheck] fn iter(v: Vec<(u8, u64)>) -> bool {
        let log_cap = (v.len() + 1).next_power_of_two().trailing_zeros();
        let mut t = mk_ht::<u8, u64, _>(1 << log_cap, DefaultHasher::default());
        for (k, x) in v.clone() { t.insert(k, x).unwrap(); }

        t.iter_with_ix().all(|(k, &i, &x)| k < 1 << log_cap &&
                                           v.iter().any(|&(j, y)| (i, x) == (j, y)))
    }

    #[test] fn full_table_forbidden() {
        let mut t = mk_ht::<u8, (), _>(2, DefaultHasher::default());
        t.insert(0, ()).unwrap();
        assert!(t.insert(1, ()).is_err());
    }
}
