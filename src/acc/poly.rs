use super::set::Set;
use ark_ff::{Field, Zero};
use core::{
    cmp, fmt,
    ops::{Add, AddAssign, Div, Mul, Sub, SubAssign},
};
use rayon::prelude::*;
use std::collections::{btree_map::Entry, BTreeMap};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Variable {
    S,
    R,
}
pub(crate) const S: Variable = Variable::S;
pub(crate) const R: Variable = Variable::R;

/// Represent S^s_pow * R^r_pow
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct Term {
    s_pow: u64,
    r_pow: u64,
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.s_pow == 0 && self.r_pow == 0 {
            Ok(())
        } else if self.r_pow == 0 {
            write!(f, "s^{}", self.s_pow)
        } else if self.s_pow == 0 {
            write!(f, "r^{}", self.r_pow)
        } else {
            write!(f, "s^{} * r^{}", self.s_pow, self.r_pow)
        }
    }
}

impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Term {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.degree()
            .cmp(&other.degree())
            .then(self.s_pow.cmp(&other.s_pow))
            .then(self.r_pow.cmp(&other.r_pow))
            .reverse()
    }
}

impl Term {
    pub(crate) fn new(s_pow: u64, r_pow: u64) -> Self {
        Term { s_pow, r_pow }
    }

    pub(crate) fn degree(self) -> u64 {
        self.s_pow + self.r_pow
    }

    pub(crate) fn get_power(self, x: Variable) -> u64 {
        match x {
            Variable::S => self.s_pow,
            Variable::R => self.r_pow,
        }
    }
}

/// Represent Poly {\sum coeff * term}
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Poly<F: Field> {
    coeffs: BTreeMap<Term, F>,
}

impl<F: Field> fmt::Debug for Poly<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for (t, c) in self.coeff_iter() {
            if first {
                first = false;
            } else {
                write!(f, " + ")?;
            }

            write!(f, "{} {:?}", c, t)?;
        }
        Ok(())
    }
}

impl<F: Field> Zero for Poly<F> {
    fn zero() -> Self {
        Poly {
            coeffs: BTreeMap::new(),
        }
    }

    fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }
}

impl<'lhs, 'rhs, F: Field> Add<&'rhs Poly<F>> for &'lhs Poly<F> {
    type Output = Poly<F>;

    fn add(self, rhs: &'rhs Poly<F>) -> Self::Output {
        let mut poly = self.clone();
        poly.add_assign(rhs);
        poly
    }
}

impl<F: Field> Add for Poly<F> {
    type Output = Poly<F>;

    fn add(self, rhs: Self) -> Self::Output {
        &self + &rhs
    }
}

impl<'rhs, F: Field> AddAssign<&'rhs Poly<F>> for Poly<F> {
    fn add_assign(&mut self, rhs: &'rhs Poly<F>) {
        for (t, c) in rhs.coeff_iter() {
            match self.coeffs.entry(*t) {
                Entry::Vacant(e) => {
                    e.insert(*c);
                }
                Entry::Occupied(mut e) => {
                    *e.get_mut() += c;
                    if e.get().is_zero() {
                        e.remove();
                    }
                }
            }
        }
    }
}

impl<'lhs, 'rhs, F: Field> Sub<&'rhs Poly<F>> for &'lhs Poly<F> {
    type Output = Poly<F>;

    fn sub(self, rhs: &'rhs Poly<F>) -> Self::Output {
        let mut poly = self.clone();
        poly.sub_assign(rhs);
        poly
    }
}

impl<F: Field> Sub for Poly<F> {
    type Output = Poly<F>;

    fn sub(self, rhs: Self) -> Self::Output {
        &self - &rhs
    }
}

impl<'rhs, F: Field> SubAssign<&'rhs Poly<F>> for Poly<F> {
    fn sub_assign(&mut self, rhs: &'rhs Poly<F>) {
        for (t, c) in rhs.coeff_iter() {
            match self.coeffs.entry(*t) {
                Entry::Vacant(e) => {
                    e.insert(-*c);
                }
                Entry::Occupied(mut e) => {
                    *e.get_mut() -= c;
                    if e.get().is_zero() {
                        e.remove();
                    }
                }
            }
        }
    }
}

impl<'lhs, 'rhs, F: Field> Mul<&'rhs Poly<F>> for &'lhs Poly<F> {
    type Output = Poly<F>;

    fn mul(self, rhs: &'rhs Poly<F>) -> Self::Output {
        if self.is_zero() || rhs.is_zero() {
            Poly::zero()
        } else {
            self.coeffs
                .par_iter()
                .flat_map(|(&lhs_term, &lhs_coeff)| {
                    rhs.coeffs.par_iter().map(move |(&rhs_term, &rhs_coeff)| {
                        let coeff = lhs_coeff * rhs_coeff;
                        let term = Term::new(
                            lhs_term.s_pow + rhs_term.s_pow,
                            lhs_term.r_pow + rhs_term.r_pow,
                        );
                        (term, coeff)
                    })
                })
                .fold(Poly::zero, |mut poly, (t, c)| {
                    match poly.coeffs.entry(t) {
                        Entry::Vacant(e) => {
                            e.insert(c);
                        }
                        Entry::Occupied(mut e) => {
                            *e.get_mut() += c;
                            if e.get().is_zero() {
                                e.remove();
                            }
                        }
                    }
                    poly
                })
                .reduce(Poly::zero, |mut poly1, poly2| {
                    poly1 += &poly2;
                    poly1
                })
        }
    }
}

impl<'lhs, 'rhs, F: Field> Div<&'rhs Poly<F>> for &'lhs Poly<F> {
    type Output = (Poly<F>, Poly<F>);

    /// Return poly {lhs / rhs} = (q, r) s.t. rhs * q + r == lhs
    fn div(self, rhs: &'rhs Poly<F>) -> Self::Output {
        let (rhs_lead_term, rhs_lead_coeff) =
            rhs.lead_term_and_coeff().expect("cannot divide by zero");

        let mut q = Poly::zero();
        let mut r = self.clone();

        while !r.is_zero() {
            let r_lead = r.coeffs.iter().find(|(term, _)| {
                term.s_pow >= rhs_lead_term.s_pow && term.r_pow >= rhs_lead_term.r_pow
            });

            let (r_lead_term, r_lead_coeff) = match r_lead {
                Some((t, c)) => (*t, *c),
                None => break,
            };

            let lead_div_coeff = r_lead_coeff / rhs_lead_coeff;
            let lead_div_term = Term::new(
                r_lead_term.s_pow - rhs_lead_term.s_pow,
                r_lead_term.r_pow - rhs_lead_term.r_pow,
            );
            q.add_nonzero_term(lead_div_term, lead_div_coeff);
            r -= &rhs.mul_nonzero_term(lead_div_term, lead_div_coeff);
        }

        (q, r)
    }
}

impl<F: Field> Poly<F> {
    /// Remove v^q term from the poly
    pub(crate) fn remove_partial_term(&mut self, v: Variable, q: u64) {
        self.coeffs.retain(|t, _c| t.get_power(v) != q);
    }

    pub(crate) fn num_terms(&self) -> usize {
        self.coeffs.len()
    }

    pub(crate) fn lead_term_and_coeff(&self) -> Option<(Term, F)> {
        self.coeffs.iter().next().map(|(t, c)| (*t, *c))
    }

    pub(crate) fn coeff_iter(&self) -> impl Iterator<Item = (&'_ Term, &'_ F)> {
        self.coeffs.iter()
    }

    pub(crate) fn add_nonzero_term(&mut self, term: Term, coeff: F) {
        match self.coeffs.entry(term) {
            Entry::Vacant(e) => {
                e.insert(coeff);
            }
            Entry::Occupied(mut e) => {
                *e.get_mut() += coeff;
                if e.get().is_zero() {
                    e.remove();
                }
            }
        }
    }

    pub(crate) fn mul_nonzero_term(&self, term: Term, coeff: F) -> Self {
        let coeffs = self
            .coeffs
            .par_iter()
            .map(|(&self_term, &self_coeff)| {
                let new_c = self_coeff * coeff;
                let new_t = Term::new(self_term.s_pow + term.s_pow, self_term.r_pow + term.r_pow);
                (new_t, new_c)
            })
            .collect();
        Poly { coeffs }
    }
}

/// Return poly {\sum x^i}
#[inline]
pub(crate) fn poly_a<F: Field>(set: &Set, x: Variable) -> Poly<F> {
    let one = F::one();
    let mut coeffs = BTreeMap::new();
    for i in set.iter() {
        let i = i.get();
        let term = match x {
            Variable::S => Term::new(i, 0),
            Variable::R => Term::new(0, i),
        };
        coeffs.insert(term, one);
    }
    Poly { coeffs }
}

/// Return poly {\sum x^i y^{q-i}}
#[inline]
pub(crate) fn poly_b<F: Field>(set: &Set, x: Variable, y: Variable, q: u64) -> Poly<F> {
    debug_assert_ne!(x, y);
    let one = F::one();
    let mut coeffs = BTreeMap::new();
    for i in set.iter() {
        let i = i.get();
        let term = match x {
            Variable::S => Term::new(i, q - i),
            Variable::R => Term::new(q - i, i),
        };
        coeffs.insert(term, one);
    }
    Poly { coeffs }
}

/// Return poly {x - 1}
#[inline]
pub(crate) fn poly_variable_minus_one<F: Field>(x: Variable) -> Poly<F> {
    let one = F::one();
    let mut coeffs = BTreeMap::new();
    let term = match x {
        Variable::S => Term::new(1, 0),
        Variable::R => Term::new(0, 1),
    };
    coeffs.insert(term, one);
    coeffs.insert(Term::new(0, 0), -one);
    Poly { coeffs }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::set;
    use ark_bls12_381::Fr;
    use ark_ff::One;

    #[test]
    fn test_set_intersection() {
        let q = 5;
        let s1 = set! {1, 2, 3};
        let s2 = set! {1, 4};
        let s1_a: Poly<Fr> = poly_a(&s1, S);
        let s2_b: Poly<Fr> = poly_b(&s2, R, S, q);
        let s3_a: Poly<Fr> = poly_a(&(&s1 & &s2), R);
        let r_q: Poly<Fr> = Poly {
            coeffs: core::iter::once((Term::new(q, 0), Fr::one())).collect(),
        };
        let p1 = &s1_a * &s2_b;
        let mut p2 = p1.clone();
        p2.remove_partial_term(S, q);
        assert_eq!(p1, p2 + (&s3_a * &r_q));
    }

    #[test]
    fn test_poly_div() {
        let q = 5;
        let s = set! {1, 2, 3};
        let s_a: Poly<Fr> = poly_a(&s, S);
        let s_b: Poly<Fr> = poly_b(&s, S, R, q);
        let p1 = &s_a - &s_b;
        let p2 = poly_variable_minus_one(R);
        let (p3, r) = &p1 / &p2;
        assert!(r.is_zero());
        assert_eq!(&p3 * &p2, p1);
    }
}
