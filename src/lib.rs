#![no_std]

extern crate siphasher as sip;
extern crate slot;

use core::borrow::Borrow;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::ops::{Index, IndexMut, RangeFull};
use core::{mem, ptr};
use slot::Slot;

#[derive(Clone)]
pub struct DefaultHasher(::sip::sip::SipHasher);

pub struct HashTable<K: Eq + Hash, T,
                     Hs: IndexMut<usize, Output = usize> + Index<RangeFull, Output = [usize]>,
                     Es: IndexMut<usize, Output = Slot<(K, T)>>, H: Clone + Hasher = DefaultHasher> {
    hashes: Hs,
    elems : Es,
    free_n: usize,
    hasher: H,
}

impl<K: Eq + Hash, T, Hs: IndexMut<usize, Output = usize> + Index<RangeFull, Output = [usize]>,
     Es: IndexMut<usize, Output = Slot<(K, T)>>, H: Clone + Hasher> HashTable<K, T, Hs, Es, H> {
    fn log_cap(&self) -> u32 { 0usize.count_zeros() - self.hashes[..].len().leading_zeros() - 1 }

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
            if self.hashes[i] == h && unsafe { self.elems[i].x.0.borrow() == k } { return Some(i); }
            i = (i+1)&wrap_mask;
            debug_assert_ne!(h & wrap_mask, i);
            psl += 1;
        }
    }

    #[inline]
    pub fn find_with_ix<Q: ?Sized>(&self, k: &Q) -> Option<(usize, &K, &T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.find_ix(k).map(move |i| unsafe { (i, &self.elems[i].x.0, &self.elems[i].x.1) })
    }

    #[inline]
    pub fn find_mut_with_ix<Q: ?Sized>(&mut self, k: &Q) -> Option<(usize, &K, &mut T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.find_ix(k).map(move |i| unsafe { let &mut (ref k, ref mut v) = &mut self.elems[i].x; (i, k, v) })
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
                ptr::write(&mut self.elems[i].x, (k, f(None)));
                let &mut (ref k, ref mut v) = &mut self.elems[i].x;
                return Ok((i, k, v))
            }

            if self.hashes[i] == h && self.elems[i].x.0 == k {
                self.hashes[i] |=  dead_flag;
                let x = ptr::read(&self.elems[i].x.1);
                ptr::write(&mut self.elems[i].x.1, f(Some(x)));
                self.hashes[i] &= !dead_flag;
                let &mut (ref k, ref mut v) = &mut self.elems[i].x;
                return Ok((i, k, v))
            }

            if psl > compute_psl(&self.hashes[..], i) {
                let mut e = (k, f(None));
                loop {
                    mem::swap(&mut h, &mut self.hashes[i]);
                    mem::swap(&mut e, &mut self.elems[i].x);
                    if h == 0 || is_dead(h) {
                        mem::forget(e);
                        let &mut (ref k, ref mut v) = &mut self.elems[i].x;
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
            let (_, x) = ptr::read(&self.elems[i]).x;
            self.hashes[i] |= dead_flag;
            x
        })
    }

    #[inline]
    pub fn iter_with_ix(&self) -> IterWithIx<K, T> {
        IterWithIx {
            φ: PhantomData,
            hash_ptr: &self.hashes[0],
            elms_ptr: &self.elems[0] as *const Slot<_> as *const _,
            hash_end: self.hashes[..].as_ptr().wrapping_offset(self.hashes[..].len() as _),
        }
    }

    #[inline]
    pub fn iter_mut_with_ix(&mut self) -> IterMutWithIx<K, T> {
        IterMutWithIx {
            φ: PhantomData,
            hash_ptr: &self.hashes[0],
            elms_ptr: &mut self.elems[0] as *mut Slot<_> as *mut _,
            hash_end: self.hashes[..].as_ptr().wrapping_offset(self.hashes[..].len() as _),
        }
    }
}

#[derive(Clone, Copy)]
pub struct IterWithIx<'a, K, T> {
    φ: PhantomData<&'a ()>,
    hash_ptr: *const usize,
    elms_ptr: *const (K, T),
    hash_end: *const usize,
}

impl<'a, K: 'a, T: 'a> Iterator for IterWithIx<'a, K, T> {
    type Item = (usize, &'a K, &'a T);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let mut r = None;
        while r.is_none() && self.hash_ptr != self.hash_end { unsafe {
            if 0 != ptr::read(self.hash_ptr) { r = Some((ptr_diff(self.hash_ptr, self.hash_end),
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
    φ: PhantomData<&'a ()>,
    hash_ptr: *const usize,
    elms_ptr: *mut (K, T),
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
            if 0 != ptr::read(self.hash_ptr) { r = Some((ptr_diff(self.hash_ptr, self.hash_end),
                                                         &    (*self.elms_ptr).0,
                                                         &mut (*self.elms_ptr).1)); }
            self.hash_ptr = self.hash_ptr.wrapping_offset(1);
            self.elms_ptr = self.elms_ptr.offset(1);
        } }
        r
    }
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
            if self.hashes[i] != 0 && !is_dead(self.hashes[i]) { ptr::drop_in_place(&mut self.elems[i].x); }
        }
    } }
}

#[inline] pub fn ptr_diff<T>(p: *const T, q: *const T) -> usize {
    use ::core::num::Wrapping as w;
    (w(p as usize) - w(q as usize)).0/mem::size_of::<T>()
}
