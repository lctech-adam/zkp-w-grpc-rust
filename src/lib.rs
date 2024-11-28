use num_bigint::BigUint;

/// output = n^exp mod p
/// ex: alpha^x mod p
pub fn exponentiate(n: &BigUint, exponent: &BigUint, modulus: &BigUint) -> BigUint {
    n.modpow(exponent, modulus)
}

/// output = s = (k - c * x) mod q
pub fn solve(k: &BigUint, c: &BigUint, x: &BigUint, q: &BigUint) -> BigUint {
    let exp = &BigUint::from(1u32);
    if *k >= c * k {
        return (k - c * x).modpow(exp, q);
    }
    return q - (c * x - k).modpow(exp, q);
}

/// condition1 = r1 = alpha^s * y1^c
/// condition2 = r2 = beta^s * y2^c
pub fn verify(
    r1: &BigUint,
    r2: &BigUint,
    y1: &BigUint,
    y2: &BigUint,
    alpha: &BigUint,
    beta: &BigUint,
    c: &BigUint,
    s: &BigUint,
    p: &BigUint,
) -> bool {
    let cond1 = *r1 == (alpha.modpow(s, p) * y1.modpow(c, p)).modpow(&BigUint::from(1u32), p);
    let cond2 = *r2 == (beta.modpow(s, p) * y2.modpow(c, p)).modpow(&BigUint::from(1u32), p);
    cond1 && cond2
}

#[derive(Debug)]
struct Verifier {
    alpha: BigUint,
    beta: BigUint,
    prime_num: BigUint,
    verifier_random_num: BigUint,
    pair_1: (BigUint, BigUint),
    pair_2: (BigUint, BigUint),
}

fn big_zero() -> BigUint {
    BigUint::from(0u32)
}

fn big_mod(num: &BigUint, modulus: &BigUint) -> BigUint {
    num.modpow(&BigUint::from(1u32), modulus)
}

impl Verifier {
    fn new(alpha: BigUint, beta: BigUint, prime_num: BigUint) -> Self {
        Self {
            alpha,
            beta,
            prime_num,
            verifier_random_num: big_zero(),
            pair_1: (big_zero(), big_zero()),
            pair_2: (big_zero(), big_zero()),
        }
    }

    pub fn set_verifier_random_num(&mut self, verifier_random_num: BigUint) {
        self.verifier_random_num = verifier_random_num
    }

    pub fn add_pair_1(&mut self, pair_1: (BigUint, BigUint)) {
        self.pair_1 = pair_1;
    }

    pub fn add_pair_2(&mut self, pair_2: (BigUint, BigUint)) {
        self.pair_2 = pair_2;
    }

    fn cond_1_valid(&self, answer: &BigUint, verifier_random_num: &BigUint) -> bool {
        let v1 = self.alpha.modpow(answer, &self.prime_num);
        let v2 = self.pair_1.0.modpow(verifier_random_num, &self.prime_num);
        let v = big_mod(&(v1 * v2), &self.prime_num);
        self.pair_2.0 == v
    }

    fn cond_2_valid(&self, answer: &BigUint, verifier_random_num: &BigUint) -> bool {
        let v1 = self.beta.modpow(answer, &self.prime_num);
        let v2 = self.pair_1.1.modpow(verifier_random_num, &self.prime_num);
        let v = big_mod(&(v1 * v2), &self.prime_num);
        self.pair_2.1 == v
    }

    pub fn submit_answer(&self, answer: &BigUint) -> bool {
        self.cond_1_valid(answer, &self.verifier_random_num)
            && self.cond_2_valid(answer, &self.verifier_random_num)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_example() {
        // constant
        let alpha = BigUint::from(4u32);
        let beta = BigUint::from(9u32);
        let prime_num = BigUint::from(23u32);
        let group_order = BigUint::from(11u32);

        let mut verifier = Verifier::new(alpha.clone(), beta.clone(), prime_num.clone());

        let prover_secret = BigUint::from(6u32);
        let prover_random_num = BigUint::from(7u32);
        let verifier_random_num = BigUint::from(4u32);

        verifier.set_verifier_random_num(verifier_random_num.clone());

        let y1 = exponentiate(&alpha, &prover_secret, &prime_num);
        let y2 = exponentiate(&beta, &prover_secret, &prime_num);
        assert_eq!(y1, BigUint::from(2u32));
        assert_eq!(y2, BigUint::from(3u32));

        verifier.add_pair_1((y1.clone(), y2.clone()));

        let r1 = exponentiate(&alpha, &prover_random_num, &prime_num);
        let r2 = exponentiate(&beta, &prover_random_num, &prime_num);
        assert_eq!(r1, BigUint::from(8u32));
        assert_eq!(r2, BigUint::from(4u32));

        verifier.add_pair_2((r1.clone(), r2.clone()));

        let answer = solve(
            &prover_random_num,
            &verifier_random_num,
            &prover_secret,
            &group_order,
        );
        assert_eq!(answer, BigUint::from(5u32));

        let is_valid = verify(
            &r1,
            &r2,
            &y1,
            &y2,
            &alpha,
            &beta,
            &verifier_random_num,
            &answer,
            &prime_num,
        );
        assert!(is_valid);

        let is_valid = verifier.submit_answer(&answer);
        assert!(is_valid);
    }
}
