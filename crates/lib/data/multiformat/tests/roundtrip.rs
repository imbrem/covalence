//! Property tests: encode/decode and CID round-trips over many generated
//! `DerivationFact`s and `Cid`s, using a deterministic LCG (no rng dep).

use covalence_multiformat::{Cid, DerivationFact, codec};

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }
    fn range(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

const CODECS: [u64; 6] = [
    codec::RAW,
    codec::AXIOM_SET,
    codec::COV_HOL_THM,
    codec::COLN_GEOM_SEQ,
    codec::MM_DERIVATION,
    codec::DERIVATION_FACT,
];
const LOGICS: [u64; 3] = [
    codec::logic::HOL,
    codec::logic::GEOMETRIC,
    codec::logic::METAMATH,
];

fn rand_cid(lcg: &mut Lcg) -> Cid {
    Cid::of(CODECS[lcg.range(CODECS.len())], &lcg.next().to_le_bytes())
}

fn rand_fact(lcg: &mut Lcg) -> DerivationFact {
    let prop_len = lcg.range(24);
    let prop = (0..prop_len).map(|_| lcg.next() as u8).collect();
    let n_assume = lcg.range(5);
    let assumptions = (0..n_assume).map(|_| rand_cid(lcg)).collect();
    DerivationFact {
        logic: LOGICS[lcg.range(LOGICS.len())],
        axioms: rand_cid(lcg),
        prop_codec: CODECS[lcg.range(CODECS.len())],
        prop,
        assumptions,
        derivation: rand_cid(lcg),
    }
}

#[test]
fn cid_roundtrips() {
    let mut lcg = Lcg(0xC1D5EED);
    for _ in 0..2000 {
        let c = rand_cid(&mut lcg);
        assert_eq!(Cid::decode(&c.encode()).unwrap(), c, "wire round-trip");
        assert_eq!(Cid::from_text(&c.to_text()).unwrap(), c, "text round-trip");
    }
}

#[test]
fn fact_roundtrips_and_cid_is_stable() {
    let mut lcg = Lcg(0xFAC7_5EED);
    for _ in 0..2000 {
        let f = rand_fact(&mut lcg);
        let body = f.encode();
        // decode∘encode = id
        assert_eq!(DerivationFact::decode(&body).unwrap(), f);
        // cid is deterministic and itself round-trips
        let cid = f.cid();
        assert_eq!(f.cid(), cid);
        assert_eq!(Cid::decode(&cid.encode()).unwrap(), cid);
        // decoding then re-encoding reproduces the same bytes (canonical)
        assert_eq!(DerivationFact::decode(&body).unwrap().encode(), body);
    }
}
