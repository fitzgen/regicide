use core::fmt;

use crate::entity::{Entity, SecondaryMap};
use alloc::vec::Vec;

pub(crate) struct UnionFind<E> {
    map: SecondaryMap<E, Option<E>>,
    stack: Vec<E>,
}

impl<E> fmt::Debug for UnionFind<E>
where
    E: Entity + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("UnionFind")
            .field("map", &self.map)
            .finish_non_exhaustive()
    }
}

impl<E> Default for UnionFind<E>
where
    E: Entity,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<E> UnionFind<E>
where
    E: Entity,
{
    pub const fn new() -> Self {
        Self {
            map: SecondaryMap::new(None),
            stack: Vec::new(),
        }
    }

    pub fn reset(&mut self) {
        let Self { map, stack } = self;
        map.reset();
        debug_assert!(stack.is_empty());
    }

    pub fn is_reset(&self) -> bool {
        let Self { map, stack } = self;
        map.is_reset() && stack.is_empty()
    }

    pub fn find_without_path_compression(&self, entry: E) -> E {
        let mut entry = entry;
        while let Some(e) = self.map[entry]
            && e != entry
        {
            entry = e;
        }
        debug_assert!(self.map[entry].is_none_or(|e| e == entry));
        entry
    }

    pub fn find(&mut self, entry: E) -> E {
        let mut entry = entry;
        while let Some(e) = self.map[entry]
            && e != entry
        {
            self.stack.push(entry);
            entry = e;
        }
        debug_assert!(self.map[entry].is_none_or(|e| e == entry));
        for e in self.stack.drain(..) {
            self.map[e] = Some(entry);
        }
        entry
    }

    pub fn union(&mut self, a: E, b: E) -> E {
        let a = self.find(a);
        let b = self.find(b);
        self.map[b] = Some(a);
        a
    }
}

#[cfg(test)]
mod tests {
    use super::UnionFind;
    use crate::{Entity, entity::Val};
    use mutatis::{
        Mutate, MutateInRange,
        check::{Check, CheckError, CheckResult},
        mutators as m,
    };
    use std::{
        collections::{HashMap, HashSet},
        string::String,
        vec::Vec,
    };

    type V = Val<u8>;

    fn v(v: u8) -> V {
        V::try_new(v as usize).unwrap()
    }

    #[test]
    fn basic() {
        let mut uf = UnionFind::new();
        let a = v(0);
        let b = v(0);
        let c = v(0);
        let d = v(0);
        let e = v(0);
        let f = v(0);
        let g = v(0);
        let h = v(0);
        let i = v(0);

        for x in [a, b, c, d, e, f, g, h, i] {
            let y = uf.find(x);
            assert_eq!(x, y);
        }

        let aa = uf.union(a, a);
        assert_eq!(aa, a);
        assert_eq!(aa, uf.find(a));

        let bc = uf.union(b, c);
        assert_eq!(bc, b);
        assert_eq!(bc, uf.find(b));
        assert_eq!(bc, uf.find(c));

        assert_eq!(d, uf.find(d));
        let dd = uf.union(d, d);
        assert_eq!(dd, d);
        assert_eq!(dd, uf.find(d));

        let bcd = uf.union(bc, d);
        assert_eq!(bcd, b);
        assert_eq!(bcd, uf.find(b));
        assert_eq!(bcd, uf.find(c));
        assert_eq!(bcd, uf.find(d));
        assert_eq!(bcd, uf.find(bc));

        let abcd = uf.union(a, bcd);
        assert_eq!(abcd, a);
        assert_eq!(abcd, uf.find(a));
        assert_eq!(abcd, uf.find(b));
        assert_eq!(abcd, uf.find(c));
        assert_eq!(abcd, uf.find(d));
        assert_eq!(abcd, uf.find(aa));
        assert_eq!(abcd, uf.find(bc));
        assert_eq!(abcd, uf.find(bcd));
        assert_eq!(abcd, uf.find(dd));
    }

    #[test]
    fn smoke() -> CheckResult<Vec<(u8, u8)>> {
        let mutator = m::default::<Vec<(u8, u8)>>().map(|ctx, vec| {
            vec.truncate(20);
            let len = vec.len() as u8;
            for (a, b) in vec {
                *a %= len;
                *b %= len;
            }
            Ok(())
        });
        Check::new().run_with(
            mutator,
            [Vec::new()],
            |input: &Vec<(u8, u8)>| -> Result<(), String> {
                let mut uf = UnionFind::new();
                for (a, b) in input {
                    let a = v(*a);
                    let b = v(*b);

                    let c = uf.union(a, b);
                    assert_eq!(uf.find(a), c);
                    assert_eq!(uf.find(b), c);
                    assert_eq!(uf.find(c), c);
                }
                Ok(())
            },
        )
    }
}
