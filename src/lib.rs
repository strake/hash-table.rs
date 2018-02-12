#![no_std]

extern crate siphasher as sip;

use core::borrow::Borrow;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::{mem, ptr, slice};

#[derive(Clone)]
pub struct DefaultHasher(::sip::sip::SipHasher);

pub struct RefMut<'a, K: 'a + Eq + Hash, T: 'a, H: Clone + Hasher = DefaultHasher> {
    φ: PhantomData<&'a [(K, T)]>,
    log_cap: u32,
    hash_ptr: *mut usize,
    elem_ptr: *mut (K, T),
    free_n: usize,
    hasher: H,
}

impl<'a, K: Eq + Hash, T, H: Clone + Hasher> RefMut<'a, K, T, H> {
    fn components_mut(&mut self) -> (&mut [usize], &mut [(K, T)]) {
        let cap = 1<<self.log_cap;
        unsafe {
            (slice::from_raw_parts_mut(self.hash_ptr, cap),
             slice::from_raw_parts_mut(self.elem_ptr, cap))
        }
    }

    fn components(&self) -> (&[usize], &[(K, T)]) { unsafe {
        let (hashes, elems) = (self as *const Self as *mut Self).as_mut().unwrap().components_mut();
        (hashes, elems)
    } }

    fn hash<Q: ?Sized>(&self, k: &Q) -> usize where Q: Hash {
        let mut h = self.hasher.clone();
        k.hash(&mut h);
        (h.finish() as usize | hash_flag) & !dead_flag
    }

    fn find_ix<Q: ?Sized>(&self, k: &Q) -> Option<usize> where K: Borrow<Q>, Q: Eq + Hash {
        debug_assert!(self.free_n >= 1);
        let wrap_mask = (1<<self.log_cap)-1;
        let h = self.hash(k);
        let mut i = h & wrap_mask;
        let mut psl = 0;
        let (hashes, elms) = self.components();
        loop {
            if hashes[i] == 0 || psl > compute_psl(hashes, i) { return None };
            if hashes[i] == h && elms[i].0.borrow() == k { return Some(i); }
            i = (i+1)&wrap_mask;
            debug_assert_ne!(h & wrap_mask, i);
            psl += 1;
        }
    }

    #[inline]
    pub fn find_with_ix<Q: ?Sized>(&self, k: &Q) -> Option<(usize, &K, &T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.find_ix(k).map(move |i| { let (_, elms) = self.components(); (i, &elms[i].0, &elms[i].1) })
    }

    #[inline]
    pub fn find_mut_with_ix<Q: ?Sized>(&mut self, k: &Q) -> Option<(usize, &K, &mut T)> where K: Borrow<Q>, Q: Eq + Hash {
        self.find_ix(k).map(move |i| { let (_, elms) = self.components_mut(); (i, &elms[i].0, &mut elms[i].1) })
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
    pub fn insert_with<F: FnOnce(Option<T>) -> T>(&mut self, k: K, f: F) -> Result<(usize, &mut K, &mut T), (K, F)> {
        if 1 >= self.free_n { return Err((k, f)); }
        self.free_n -= 1;

        let cap = 1<<self.log_cap;
        let mut h = self.hash(&k);
        let mut i = h&(cap-1);
        let mut psl = 0;
        let (hashes, elms) = self.components_mut();
        loop {
            if hashes[i] == 0 {
                hashes[i] = h;
                unsafe { ptr::write(&mut elms[i], (k, f(None))); }
                return Ok((i, &mut elms[i].0, &mut elms[i].1))
            }

            if hashes[i] == h && elms[i].0 == k {
                unsafe {
                    hashes[i] |=  dead_flag;
                    let x = ptr::read(&elms[i].1);
                    ptr::write(&mut elms[i].1, f(Some(x)));
                    hashes[i] &= !dead_flag;
                }
                return Ok((i, &mut elms[i].0, &mut elms[i].1))
            }

            if psl > compute_psl(hashes, i) {
                let mut e = (k, f(None));
                loop {
                    mem::swap(&mut h, &mut hashes[i]);
                    mem::swap(&mut e, &mut elms[i]);
                    if h == 0 || is_dead(h) {
                        mem::forget(e);
                        return Ok((i, &mut elms[i].0, &mut elms[i].1));
                    };
                    i = (i+1)&(cap-1);
                }
            }

            i = (i+1)&(cap-1);
            debug_assert_ne!(h&(cap-1), i);
            psl += 1;
        }
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
            debug_assert!(1 << self.log_cap >= self.free_n);
            let (hashes, elms) = self.components_mut();
            let (_, x) = ptr::read(&elms[i]);
            hashes[i] |= dead_flag;
            x
        })
    }
}

#[inline] fn compute_psl(hs: &[usize], i: usize) -> usize { usize::wrapping_sub(i, hs[i])&(hs.len()-1) }

#[inline] fn is_dead(h: usize) -> bool { 0 != h & dead_flag }

const dead_flag: usize = !(!0>>1);
const hash_flag: usize = dead_flag>>1;
