use std::{
    collections::HashSet,
    hash::Hash,
    ops::{BitAnd, BitOr, BitXor, BitXorAssign, Not},
};

pub trait Term:
    Eq
    + Ord
    + Hash
    + Clone
    + BitXor<Output = Anf<Self>>
    + Not<Output = Anf<Self>>
    + BitAnd
    + BitOr<Output = Anf<Self>>
{
    fn unit() -> Self;
    fn is_subset(&self, other: &Self) -> bool;
    fn extended(self, other: &Self) -> Self;
    fn nth(n: usize) -> Self;
}

macro_rules! bit_term_impl {
    ($([$BitTerm:ident, $UInt:ty]),* $(,)?) => {
        $(
            #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
            pub struct $BitTerm($UInt);

            impl $BitTerm {
                pub fn new(raw: $UInt) -> Self {
                    Self(raw)
                }
            }

            impl Term for $BitTerm {
                fn unit() -> Self {
                    Self(0)
                }

                fn is_subset(&self, other: &Self) -> bool {
                    self.0 & other.0 == self.0
                }

                fn extended(self, other: &Self) -> Self {
                    Self(self.0 | other.0)
                }

                fn nth(n: usize) -> Self {
                    assert!(n < <$UInt>::BITS as usize);
                    Self(1 << n)
                }
            }

            impl BitXor for $BitTerm {
                type Output = Anf<Self>;

                fn bitxor(self, rhs: Self) -> Self::Output {
                    Anf::from_iter([self, rhs])
                }
            }

            impl Not for $BitTerm {
                type Output = Anf<Self>;

                fn not(self) -> Self::Output {
                    if self == Self::unit() {
                        Anf::zero()
                    } else {
                        Anf::from_iter([Self::unit(), self])
                    }
                }
            }

            impl BitAnd for $BitTerm {
                type Output = Self;

                fn bitand(self, rhs: Self) -> Self::Output {
                    self.extended(&rhs)
                }
            }

            impl BitOr for $BitTerm {
                type Output = Anf<Self>;

                fn bitor(self, rhs: Self) -> Self::Output {
                    Anf::from_iter([self, rhs, self & rhs])
                }
            }
        )*
    };
}

bit_term_impl!(
    [BitTerm8, u8],
    [BitTerm16, u16],
    [BitTerm32, u32],
    [BitTerm64, u64],
    [BitTerm128, u128],
);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Anf<T: Term>(HashSet<T>);

impl<T: Term> Anf<T> {
    pub fn zero() -> Self {
        Self(HashSet::new())
    }

    pub fn unit() -> Self {
        T::unit().into()
    }

    pub fn evaluate(&self, variables: &T) -> bool {
        self.0
            .iter()
            .fold(false, |value, term| value ^ term.is_subset(variables))
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl<T: Term> From<T> for Anf<T> {
    fn from(term: T) -> Self {
        Self(HashSet::from([term]))
    }
}

impl<T: Term> BitXorAssign<T> for Anf<T> {
    fn bitxor_assign(&mut self, term: T) {
        if !self.0.remove(&term) {
            self.0.insert(term);
        }
    }
}

impl<T: Term> BitXor<T> for Anf<T> {
    type Output = Self;

    fn bitxor(mut self, term: T) -> Self::Output {
        self ^= term;
        self
    }
}

impl<T: Term> Extend<T> for Anf<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        iter.into_iter().for_each(|term| *self ^= term);
    }
}

impl<T: Term> BitXor for Anf<T> {
    type Output = Self;

    fn bitxor(mut self, rhs: Self) -> Self::Output {
        self.extend(rhs.0);
        self
    }
}

impl<T: Term> FromIterator<T> for Anf<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut anf = Self::zero();
        anf.extend(iter);
        anf
    }
}

impl<T: Term> Not for Anf<T> {
    type Output = Self;

    fn not(self) -> Self::Output {
        self ^ T::unit()
    }
}

impl<T: Term> BitAnd for Anf<T> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        // TODO: Optimize for the unit term case.
        Self::from_iter(
            self.0
                .into_iter()
                .flat_map(|a| rhs.0.iter().map(move |b| a.clone().extended(b))),
        )
    }
}

impl<T: Term> BitAnd<T> for Anf<T> {
    type Output = Self;

    fn bitand(self, term: T) -> Self::Output {
        // TODO: Deduplicate code.
        if term != T::unit() {
            Self::from_iter(self.0.into_iter().map(|curr| curr.extended(&term)))
        } else {
            self
        }
    }
}

impl<T: Term> BitOr for Anf<T> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        // TODO: Optimize.
        self.clone() ^ rhs.clone() ^ (self & rhs)
    }
}

impl<T: Term> BitOr<T> for Anf<T> {
    type Output = Self;

    fn bitor(self, term: T) -> Self::Output {
        // TODO: Optimize.
        self.clone() ^ term.clone() ^ (self & term)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use BitTerm128 as T;

    #[test]
    fn not() {
        assert_eq!(!Anf::<T>::zero(), Anf::unit());
        assert_eq!(!Anf::<T>::unit(), Anf::zero());
    }

    #[test]
    fn formula() {
        assert_eq!(
            (!T::nth(2) & T::nth(1)) | T::nth(0),
            Anf::from_iter([
                T::new(0b001),
                T::new(0b010),
                T::new(0b011),
                T::new(0b110),
                T::new(0b111),
            ])
        );
    }

    #[test]
    fn not_a_and_a() {
        assert_eq!(!T::nth(0) & T::nth(0), Anf::zero());
    }

    #[test]
    fn or_subsumption() {
        assert_eq!(
            T::new(0b01) | T::new(0b10) | T::new(0b11),
            Anf::from_iter([T::new(0b01), T::new(0b10), T::new(0b11)]),
        );
    }
}
