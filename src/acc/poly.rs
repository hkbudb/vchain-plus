use super::set::Set;
use ark_ff::{Field, Zero};
use ark_poly::{
    multivariate::{SparsePolynomial, SparseTerm, Term},
    MVPolynomial,
};
use core::cmp;

pub(crate) type Poly<F> = SparsePolynomial<F, SparseTerm>;
pub(crate) type Variable = usize;
pub(crate) const S: Variable = 0;
pub(crate) const R: Variable = 1;

/// Return i from term (x^i*y^j*...)
#[inline]
pub(crate) fn get_term_power(term: &SparseTerm, x: Variable) -> usize {
    term.iter().find(|(v, _p)| *v == x).map_or(0, |(_v, p)| *p)
}

/// Return poly {\sum x^i}
#[inline]
pub(crate) fn poly_a<F: Field>(set: &Set, x: Variable) -> Poly<F> {
    let terms: Vec<_> = set
        .iter()
        .map(|i| (F::one(), SparseTerm::new(vec![(x, i.get() as usize)])))
        .collect();
    Poly::from_coefficients_vec(2, terms)
}

/// Return poly {\sum x^i y^{q-i}}
#[inline]
pub(crate) fn poly_b<F: Field>(set: &Set, x: Variable, y: Variable, q: u64) -> Poly<F> {
    let terms: Vec<_> = set
        .iter()
        .map(|i| {
            let i = i.get();
            (
                F::one(),
                SparseTerm::new(vec![(x, i as usize), (y, (q - i) as usize)]),
            )
        })
        .collect();
    Poly::from_coefficients_vec(2, terms)
}

/// Return poly {x - 1}
#[inline]
pub(crate) fn poly_variable_minus_one<F: Field>(x: Variable) -> Poly<F> {
    Poly::from_coefficients_vec(
        2,
        vec![
            (F::one(), SparseTerm::new(vec![(x, 1)])),
            (-F::one(), SparseTerm::new(vec![])),
        ],
    )
}

/// Return poly {lhs * rhs}
pub(crate) fn poly_mul<F: Field>(lhs: &Poly<F>, rhs: &Poly<F>) -> Poly<F> {
    if lhs.is_zero() || rhs.is_zero() {
        Poly::zero()
    } else {
        let mut result_terms = Vec::new();
        for (lhs_coeff, lhs_term) in lhs.terms.iter() {
            for (rhs_coeff, rhs_term) in rhs.terms.iter() {
                let term: Vec<_> = lhs_term.iter().chain(rhs_term.iter()).copied().collect();
                let term = SparseTerm::new(term);
                result_terms.push((*lhs_coeff * *rhs_coeff, term));
            }
        }
        Poly::from_coefficients_vec(cmp::max(lhs.num_vars, rhs.num_vars), result_terms)
    }
}

/// Return poly {lhs / rhs} = (q, r) s.t. rhs * q + r == lhs
pub(crate) fn poly_div<F: Field>(lhs: &Poly<F>, rhs: &Poly<F>) -> (Poly<F>, Poly<F>) {
    let num_vars = cmp::max(lhs.num_vars, rhs.num_vars);

    let (rhs_lead_coeff, rhs_lead_term) = rhs
        .terms
        .iter()
        .max_by_key(|(_, term)| term.degree())
        .cloned()
        .expect("failed to find the lead term in rhs.");

    let mut q = Poly::zero();
    let mut r = lhs.clone();
    while !r.is_zero() {
        let r_lead = r
            .terms
            .iter()
            .filter(|(_, term)| {
                rhs_lead_term
                    .iter()
                    .all(|(l_v, l_p)| term.iter().any(|(v, p)| v == l_v && p >= l_p))
            })
            .max_by_key(|(_, term)| term.degree())
            .cloned();
        let (r_lead_coeff, r_lead_term) = match r_lead {
            Some(lead) => lead,
            None => break,
        };

        let lead_div_coeff = r_lead_coeff / rhs_lead_coeff;
        let lead_div_term = {
            let term: Vec<_> = r_lead_term
                .iter()
                .map(|(v, p)| {
                    let l_p = get_term_power(&rhs_lead_term, *v);
                    (*v, *p - l_p)
                })
                .collect();
            SparseTerm::new(term)
        };
        let div = Poly::from_coefficients_vec(num_vars, vec![(lead_div_coeff, lead_div_term)]);
        q += &div;
        r -= &poly_mul(rhs, &div);
    }
    (q, r)
}

/// Remove v^q term from the poly
#[inline]
pub(crate) fn poly_remove_term<F: Field>(input: &Poly<F>, v: Variable, q: u64) -> Poly<F> {
    let removed_term = (v, q as usize);
    let terms: Vec<_> = input
        .terms
        .iter()
        .filter(|(_, t)| !t.contains(&removed_term))
        .cloned()
        .collect();
    Poly::from_coefficients_vec(input.num_vars, terms)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::set;
    use ark_bls12_377::Fr;
    use ark_ff::One;

    #[test]
    fn test_set_intersection() {
        let q = 5;
        let s1 = set! {1, 2, 3};
        let s2 = set! {1, 4};
        let s1_a: Poly<Fr> = poly_a(&s1, S);
        let s2_b: Poly<Fr> = poly_b(&s2, R, S, q);
        let s3_a: Poly<Fr> = poly_a(&(&s1 & &s2), R);
        let r_q: Poly<Fr> = Poly::from_coefficients_vec(
            2,
            vec![(Fr::one(), SparseTerm::new(vec![(S, q as usize)]))],
        );
        let p1 = poly_mul(&s1_a, &s2_b);
        let p2 = poly_remove_term(&p1, S, q);
        assert_eq!(p1, p2 + poly_mul(&s3_a, &r_q));
    }

    #[test]
    fn test_poly_div() {
        let q = 5;
        let s = set! {1, 2, 3};
        let s_a: Poly<Fr> = poly_a(&s, S);
        let s_b: Poly<Fr> = poly_b(&s, S, R, q);
        let p1 = &s_a - &s_b;
        let p2 = poly_variable_minus_one(R);
        let (p3, r) = poly_div(&p1, &p2);
        assert!(r.is_zero());
        assert_eq!(poly_mul(&p3, &p2), p1);
    }
}
