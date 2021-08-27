use ark_ec::ProjectiveCurve;
use ark_ff::{BigInteger, FpParameters, PrimeField};

// Ref: https://github.com/blynn/pbc/blob/fbf4589036ce4f662e2d06905862c9e816cf9d08/arith/field.c#L251-L330
pub struct FixedBaseCurvePow<G: ProjectiveCurve> {
    table: Vec<Vec<G>>,
}

impl<G: ProjectiveCurve> FixedBaseCurvePow<G> {
    const K: usize = 5;

    pub fn build(base: &G) -> Self {
        let bits =
            <<G as ProjectiveCurve>::ScalarField as PrimeField>::Params::MODULUS_BITS as usize;
        let num_lookups = bits / Self::K + 1;
        let lookup_size = (1 << Self::K) - 1;
        let last_lookup_size = (1 << (bits - (num_lookups - 1) * Self::K)) - 1;

        let mut table: Vec<Vec<G>> = Vec::with_capacity(num_lookups);

        let mut multiplier = *base;
        for i in 0..num_lookups {
            let table_size = if i == num_lookups - 1 {
                last_lookup_size
            } else {
                lookup_size
            };
            let sub_table: Vec<G> = itertools::unfold(multiplier, |last| {
                let ret = *last;
                last.add_assign(&multiplier);
                Some(ret)
            })
            .take(table_size)
            .collect();
            table.push(sub_table);
            if i != num_lookups - 1 {
                let last = *table
                    .last()
                    .expect("cannot access table last")
                    .last()
                    .expect("cannot access last");
                multiplier.add_assign(&last);
            }
        }
        Self { table }
    }

    pub fn apply(&self, input: &<G as ProjectiveCurve>::ScalarField) -> G {
        let mut res = G::zero();
        let input_repr = input.into_repr();
        let num_lookups = input_repr.num_bits() as usize / Self::K + 1;
        for i in 0..num_lookups {
            let mut word: usize = 0;
            for j in 0..Self::K {
                if input_repr.get_bit(i * Self::K + j) {
                    word |= 1 << j;
                }
            }
            if word > 0 {
                res.add_assign(&self.table[i][word - 1]);
            }
        }
        res
    }
}

pub struct FixedBaseScalarPow<F: PrimeField> {
    table: Vec<Vec<F>>,
}

impl<F: PrimeField> FixedBaseScalarPow<F> {
    const K: usize = 8;

    pub fn build(base: &F) -> Self {
        let bits = <F as PrimeField>::Params::MODULUS_BITS as usize;
        let num_lookups = bits / Self::K + 1;
        let lookup_size = (1 << Self::K) - 1;
        let last_lookup_size = (1 << (bits - (num_lookups - 1) * Self::K)) - 1;

        let mut table: Vec<Vec<F>> = Vec::with_capacity(num_lookups);

        let mut multiplier = *base;
        for i in 0..num_lookups {
            let table_size = if i == num_lookups - 1 {
                last_lookup_size
            } else {
                lookup_size
            };
            let sub_table: Vec<F> = itertools::unfold(multiplier, |last| {
                let ret = *last;
                last.mul_assign(&multiplier);
                Some(ret)
            })
            .take(table_size)
            .collect();
            table.push(sub_table);
            if i != num_lookups - 1 {
                let last = *table
                    .last()
                    .expect("cannot access table last")
                    .last()
                    .expect("cannot access last");
                multiplier.mul_assign(&last);
            }
        }
        Self { table }
    }

    pub fn apply(&self, input: &F) -> F {
        let mut res = F::one();
        let input_repr = input.into_repr();
        let num_lookups = input_repr.num_bits() as usize / Self::K + 1;
        for i in 0..num_lookups {
            let mut word: usize = 0;
            for j in 0..Self::K {
                if input_repr.get_bit(i * Self::K + j) {
                    word |= 1 << j;
                }
            }
            if word > 0 {
                res.mul_assign(&self.table[i][word - 1]);
            }
        }
        res
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bn254::{Fr, G1Projective, G2Projective};
    use ark_ff::Field;
    use core::ops::MulAssign;
    use rand::Rng;

    #[test]
    fn test_pow_g1() {
        let g1p = FixedBaseCurvePow::build(&G1Projective::prime_subgroup_generator());
        let mut rng = rand::thread_rng();
        let num: Fr = rng.gen();
        let mut expect = G1Projective::prime_subgroup_generator();
        expect.mul_assign(num);
        assert_eq!(g1p.apply(&num), expect);
    }

    #[test]
    fn test_pow_g2() {
        let g2p = FixedBaseCurvePow::build(&G2Projective::prime_subgroup_generator());
        let mut rng = rand::thread_rng();
        let num: Fr = rng.gen();
        let mut expect = G2Projective::prime_subgroup_generator();
        expect.mul_assign(num);
        assert_eq!(g2p.apply(&num), expect);
    }

    #[test]
    fn test_pow_fr() {
        let mut rng = rand::thread_rng();
        let base: Fr = rng.gen();
        let num: Fr = rng.gen();
        let frp = FixedBaseScalarPow::build(&base);
        let expect = base.pow(num.into_repr());
        assert_eq!(frp.apply(&num), expect);
    }
}
