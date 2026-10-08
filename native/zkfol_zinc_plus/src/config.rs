//! The one pinned Zinc+ configuration, at three cell widths.
//!
//! zinc-plus parameterizes its protocol over a tower of type choices
//! (ZincTypes, holding three ZipTypes, one PCS instantiation per column
//! type) but ships no concrete instantiation outside its e2e bench. The
//! tier macro is that instantiation, written once: unit structs, no
//! type parameters, no restated bounds. The shared choices mirror the
//! bench: i128 challenges, a Montgomery field over three u64 limbs,
//! Miller-Rabin, IPRS over F65537. A tier is its cell, codeword, and
//! combination-ring types; binary columns keep i64 codewords at every
//! width, since bits never hold big values.

use crypto_bigint::U64;
use crypto_primitives::{
    crypto_bigint_int::Int, crypto_bigint_monty::MontyField, crypto_bigint_uint::Uint,
};
use zinc_poly::univariate::{
    binary::{BinaryPoly, BinaryPolyInnerProduct},
    dense::{DensePolyInnerProduct, DensePolynomial},
};
use zinc_primality::MillerRabin;
use zinc_protocol::ZincTypes;
use zinc_utils::inner_product::{MBSInnerProduct, ScalarProduct};
use zip_plus::{
    code::iprs::{IprsCode, PnttConfig7340033},
    pcs::structs::{ZipPlus, ZipPlusParams, ZipTypes},
};

/// Degree + 1 of the protocol's polynomials, including the trace.
pub const D: usize = 32;
const INT_LIMBS: usize = U64::LIMBS;
/// Four limbs: main-beta projects through the fixed secp256k1 prime,
/// so the modulus type must hold exactly 256 bits.
pub const FIELD_LIMBS: usize = U64::LIMBS * 4;
/// Repetition factor for the linear code, an inverse rate.
const REP_FACTOR: usize = 8;
/// Prover-side self-checks, off in earnest runs as in the upstream bench.
pub const PERFORM_CHECKS: bool = zinc_utils::UNCHECKED;
/// Overflow-checked arithmetic in the codes and the verifier: a combination
/// that wrapped would hold only modulo 2^k, where the code is far sparser.
pub const CHECK_OVERFLOW: bool = zinc_utils::CHECKED;

pub type F = MontyField<FIELD_LIMBS>;
type Fmod = Uint<FIELD_LIMBS>;
type Chal = i128;

type CombR = Int<{ INT_LIMBS * 6 }>;
pub type BigInt = Int<12>;
type BigCw = Int<13>;
type BigCombR = Int<18>;
pub type HugeInt = Int<110>;
type HugeCw = Int<111>;
type HugeCombR = Int<113>;

/// One width tier: the PCS over binary, arbitrary, and integer columns,
/// the ZincTypes wiring, the public-parameter tuple, and its setup.
macro_rules! tier {
    ($doc:literal, $binary:ident, $arbitrary:ident, $int_cfg:ident, $cfg:ident,
     $pp:ident, $setup:ident, $int:ty, $cw:ty, $comb:ty) => {
        #[doc = concat!("The PCS over binary-polynomial columns, ", $doc)]
        #[derive(Clone, Copy, Debug)]
        pub struct $binary;

        impl ZipTypes for $binary {
            const NUM_COLUMN_OPENINGS: usize = 100;
            type Eval = BinaryPoly<D>;
            type Cw = DensePolynomial<i64, D>;
            type Fmod = Fmod;
            type PrimeTest = MillerRabin;
            type Chal = Chal;
            type Pt = i128;
            type CombR = $comb;
            type Comb = DensePolynomial<$comb, D>;
            type EvalDotChal = BinaryPolyInnerProduct<Chal, D>;
            type CombDotChal = DensePolyInnerProduct<$comb, Chal, $comb, MBSInnerProduct, D>;
            type ArrCombRDotChal = MBSInnerProduct;
        }

        #[doc = concat!("The PCS over arbitrary-polynomial columns, ", $doc)]
        #[derive(Clone, Copy, Debug)]
        pub struct $arbitrary;

        impl ZipTypes for $arbitrary {
            const NUM_COLUMN_OPENINGS: usize = 100;
            type Eval = DensePolynomial<$int, D>;
            type Cw = DensePolynomial<$cw, D>;
            type Fmod = Fmod;
            type PrimeTest = MillerRabin;
            type Chal = Chal;
            type Pt = i128;
            type CombR = $comb;
            type Comb = DensePolynomial<$comb, D>;
            type EvalDotChal = DensePolyInnerProduct<$int, Chal, $comb, MBSInnerProduct, D>;
            type CombDotChal = DensePolyInnerProduct<$comb, Chal, $comb, MBSInnerProduct, D>;
            type ArrCombRDotChal = MBSInnerProduct;
        }

        #[doc = concat!("The PCS over integer columns, ", $doc)]
        #[derive(Clone, Copy, Debug)]
        pub struct $int_cfg;

        impl ZipTypes for $int_cfg {
            const NUM_COLUMN_OPENINGS: usize = 100;
            type Eval = $int;
            type Cw = $cw;
            type Fmod = Fmod;
            type PrimeTest = MillerRabin;
            type Chal = Chal;
            type Pt = i128;
            type CombR = $comb;
            type Comb = $comb;
            type EvalDotChal = ScalarProduct;
            type CombDotChal = ScalarProduct;
            type ArrCombRDotChal = MBSInnerProduct;
        }

        #[doc = concat!("The protocol configuration ", $doc)]
        #[derive(Clone, Copy, Debug)]
        pub struct $cfg;

        impl ZincTypes<D> for $cfg {
            type Int = $int;
            type Chal = Chal;
            type Pt = i128;
            type Fmod = Fmod;
            type PrimeTest = MillerRabin;

            type BinaryZt = $binary;
            type ArbitraryZt = $arbitrary;
            type IntZt = $int_cfg;

            type BinaryLc = IprsCode<$binary, PnttConfig7340033, REP_FACTOR, CHECK_OVERFLOW>;
            type ArbitraryLc = IprsCode<$arbitrary, PnttConfig7340033, REP_FACTOR, CHECK_OVERFLOW>;
            type IntLc = IprsCode<$int_cfg, PnttConfig7340033, REP_FACTOR, CHECK_OVERFLOW>;
        }

        pub type $pp = (
            ZipPlusParams<$binary, IprsCode<$binary, PnttConfig7340033, REP_FACTOR, CHECK_OVERFLOW>>,
            ZipPlusParams<
                $arbitrary,
                IprsCode<$arbitrary, PnttConfig7340033, REP_FACTOR, CHECK_OVERFLOW>,
            >,
            ZipPlusParams<
                $int_cfg,
                IprsCode<$int_cfg, PnttConfig7340033, REP_FACTOR, CHECK_OVERFLOW>,
            >,
        );

        /// Public parameters: row size equal to poly size, flat single-row matrices.
        /// The optimal-depth heuristic wants 8^depth | rows; traces under
        /// 64 rows sit below that grain, so they take the deepest depth
        /// that divides.
        pub fn $setup(num_vars: usize) -> Result<$pp, String> {
            let poly_size = 1 << num_vars;

            // One block per tuple slot, each inferring its own code type.
            macro_rules! code {
                () => {
                    IprsCode::new_with_optimal_depth(poly_size)
                        .or_else(|_| IprsCode::new(poly_size, num_vars / 3))
                        .map_err(|e| format!("code setup: {e:?}"))?
                };
            }

            Ok((
                ZipPlus::setup(poly_size, code!()),
                ZipPlus::setup(poly_size, code!()),
                ZipPlus::setup(poly_size, code!()),
            ))
        }
    };
}

tier!(
    "at i64 cells, the bench's own width.",
    BinaryCfg,
    ArbitraryCfg,
    IntCfg,
    Cfg,
    Pp,
    setup_pp,
    i64,
    i128,
    CombR
);

tier!(
    "at 768-bit cells, for big-value statements.",
    BigBinaryCfg,
    BigArbitraryCfg,
    BigIntCfg,
    BigCfg,
    BigPp,
    setup_big_pp,
    BigInt,
    BigCw,
    BigCombR
);

tier!(
    "at 7040-bit cells, for the flagship statements.",
    HugeBinaryCfg,
    HugeArbitraryCfg,
    HugeIntCfg,
    HugeCfg,
    HugePp,
    setup_huge_pp,
    HugeInt,
    HugeCw,
    HugeCombR
);
