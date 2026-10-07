//! The interpreted UAIR: signature and constraint fed from Elixir terms.
//!
//! zinc-plus's Uair trait is static (no self), so the spec lives in a
//! module global whose only writer is the prover thread: one statement
//! owns it from dequeue until its verdict.

use std::any::{Any, TypeId};
use std::collections::BTreeMap;
use std::sync::Mutex;

use serde::{Deserialize, Serialize};

use zinc_poly::{mle::DenseMultilinearExtension, univariate::dense::DensePolynomial};
use zinc_uair::{
    ideal::DegreeOneIdeal, ConstraintBuilder, LookupColumnSpec, LookupTableType, PointTie,
    PublicColumnLayout, ShiftSpec, TotalColumnLayout, TraceRow, Uair, UairSignature, UairTrace,
};

use crate::config::D;

/// One Selected lookup group: the int columns it spans, the multiset each
/// of its claims holds, and the cells of each claim as `(slot, row)`, the
/// slot indexing `columns`. Every column of the group declares the same
/// table, which is how the backend knows they are one group.
#[derive(Clone, Debug, rustler::NifStruct, Serialize, Deserialize)]
#[module = "Zkfol.ZincPlus.Selected"]
pub struct Selected {
    pub columns: Vec<usize>,
    pub values: Vec<u64>,
    pub selections: Vec<Vec<(u32, u32)>>,
}

/// One Permuted lookup group: the int columns it spans and its pairs of
/// selections, each a `(slot, row)` list; each pair holds one multiset.
#[derive(Clone, Debug, rustler::NifStruct, Serialize, Deserialize)]
#[module = "Zkfol.ZincPlus.Permuted"]
pub struct Permuted {
    pub columns: Vec<usize>,
    pub pairs: Vec<(Vec<(u32, u32)>, Vec<(u32, u32)>)>,
}

/// What a tied cell is fixed to: an int column the cell's private value
/// fills at every row.
#[derive(Clone, Debug, rustler::NifTaggedEnum, Serialize, Deserialize)]
pub enum TieTarget {
    Broadcast(usize),
}

/// One cell the statement fixes: its int column, its cube row, and what
/// fixes it. Nothing of a tie is committed and no lookup discharges it.
#[derive(Clone, Debug, rustler::NifStruct, Serialize, Deserialize)]
#[module = "Zkfol.ZincPlus.Tie"]
pub struct Tie {
    pub column: usize,
    pub row: usize,
    pub target: TieTarget,
}

/// One postfix op of the constraint program.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Op {
    Up(usize),
    Down(usize),
    Const(i64),
    Add,
    Mul,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Spec {
    pub num_cols: usize,
    pub num_public: usize,
    pub shifts: Vec<(usize, usize)>,
    pub program: Vec<Op>,
    /// Word lookups: (int column, table width, chunk width). A cell of an
    /// int column is the number the table is indexed by, so this is the
    /// range check: the column proves only if every cell is under 2^width.
    pub word_lookups: Vec<(usize, usize, usize)>,
    /// The Selected groups, one a table: each names its own cells, so it
    /// says nothing about the rows no selection reaches.
    pub selected: Vec<Selected>,
    /// The Permuted groups, one a table, each naming its pairs of cells.
    pub permuted: Vec<Permuted>,
    /// The cells the statement fixes. A named position is public
    /// structure, so the verifier evaluates each indicator itself and the
    /// proof carries nothing for one.
    pub point_ties: Vec<Tie>,
    /// Composed reads: (value_row, bit_rows, result_row), int-section
    /// indices; the pointer query binds them.
    pub reads: Vec<(usize, Vec<usize>, usize)>,
}

pub static SPEC: Mutex<Option<Spec>> = Mutex::new(None);

fn spec() -> Spec {
    SPEC.lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .clone()
        .expect("runtime uair spec unset")
}

/// Constant scalars at leaked stable addresses, one per (cell type, value).
/// zinc's projection cache keys scalars by raw pointer, so stack temporaries
/// alias each other and resolve as the wrong constant.
static CONSTS: Mutex<BTreeMap<(TypeId, i64), &'static (dyn Any + Send + Sync)>> =
    Mutex::new(BTreeMap::new());

/// The stable home of constant `k` at cell type `I`, allocated once for the process.
fn const_scalar<I>(k: i64) -> &'static DensePolynomial<I, D>
where
    I: crypto_primitives::ConstIntSemiring + From<i64> + 'static,
{
    let mut consts = CONSTS
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let entry: &'static (dyn Any + Send + Sync) = *consts
        .entry((TypeId::of::<I>(), k))
        .or_insert_with(|| Box::leak(Box::new(DensePolynomial::<I, D>::new([I::from(k)]))));
    entry
        .downcast_ref()
        .expect("const table entry matches its TypeId key")
}

#[derive(Clone, Debug)]
pub struct RuntimeUair<I>(std::marker::PhantomData<I>);

impl<I> Uair for RuntimeUair<I>
where
    I: crypto_primitives::ConstIntSemiring + From<i64> + 'static,
{
    type Ideal = DegreeOneIdeal<I>;
    type Scalar = DensePolynomial<I, D>;

    fn signature() -> UairSignature {
        let spec = spec();
        let total = TotalColumnLayout::new(0, 0, spec.num_cols);
        let public = PublicColumnLayout::new(0, 0, spec.num_public);
        let shifts = spec
            .shifts
            .iter()
            .map(|&(col, amount)| ShiftSpec::new(col, amount))
            .collect();
        let lookups = spec
            .word_lookups
            .iter()
            .map(|&(col, width, chunk)| LookupColumnSpec {
                column_index: col,
                table_type: LookupTableType::Word {
                    width,
                    chunk_width: Some(chunk),
                },
            })
            .chain(spec.selected.iter().flat_map(|group| {
                group.columns.iter().map(|&col| LookupColumnSpec {
                    column_index: col,
                    table_type: LookupTableType::Selected {
                        values: group.values.clone(),
                        selections: group.selections.clone(),
                    },
                })
            }))
            .chain(spec.permuted.iter().flat_map(|group| {
                group.columns.iter().map(|&col| LookupColumnSpec {
                    column_index: col,
                    table_type: LookupTableType::Permuted { pairs: group.pairs.clone() },
                })
            }))
            .collect();
        let reads = spec
            .reads
            .iter()
            .map(|(value, bits, result)| zinc_uair::ComposedReadSpec {
                value_col: *value,
                bit_cols: bits.clone(),
                result_col: *result,
            })
            .collect();
        let ties = spec
            .point_ties
            .iter()
            .map(|tie| match tie.target {
                TieTarget::Broadcast(into) => PointTie::broadcast(tie.column, tie.row, into),
            })
            .collect();

        UairSignature::new(total, public, shifts, lookups, vec![])
            .with_composed_reads(reads)
            .with_point_ties(ties)
    }

    fn constrain_general<B, FromR, MBS, IFromR>(
        b: &mut B,
        up: TraceRow<B::Expr>,
        down: TraceRow<B::Expr>,
        from_ref: FromR,
        _mbs: MBS,
        _ideal_from_ref: IFromR,
    ) where
        B: ConstraintBuilder,
        FromR: Fn(&Self::Scalar) -> B::Expr,
        MBS: Fn(&B::Expr, &Self::Scalar) -> Option<B::Expr>,
        IFromR: Fn(&Self::Ideal) -> B::Ideal,
    {
        let spec = spec();
        let mut stack: Vec<B::Expr> = Vec::new();

        for op in &spec.program {
            match op {
                Op::Up(col) => stack.push(up.int[*col].clone()),
                Op::Down(idx) => stack.push(down.int[*idx].clone()),
                Op::Const(k) => stack.push(from_ref(const_scalar::<I>(*k))),
                Op::Add => {
                    let rhs = stack.pop().expect("add rhs");
                    let lhs = stack.pop().expect("add lhs");
                    stack.push(lhs + &rhs);
                }
                Op::Mul => {
                    let rhs = stack.pop().expect("mul rhs");
                    let lhs = stack.pop().expect("mul lhs");
                    stack.push(lhs * &rhs);
                }
            }
        }

        let root = stack.pop().expect("program leaves one root");
        assert!(stack.is_empty(), "program leaves exactly one root");
        b.assert_zero(root);
    }
}

/// Build the trace from evaluation columns, each already padded to
/// 2^num_vars rows.
pub fn trace(columns: Vec<Vec<i64>>, num_vars: usize) -> UairTrace<'static, i64, i64, D> {
    let int = columns
        .into_iter()
        .map(|evals| DenseMultilinearExtension::from_evaluations_vec(num_vars, evals, 0i64))
        .collect::<Vec<_>>();

    UairTrace {
        binary_poly: std::borrow::Cow::Owned(vec![]),
        arbitrary_poly: std::borrow::Cow::Owned(vec![]),
        int: std::borrow::Cow::Owned(int),
    }
}

/// A wide trace from sign-free u64 limb lists, at any cell width.
pub fn limb_trace<const N: usize>(
    columns: Vec<Vec<Vec<u64>>>,
    num_vars: usize,
) -> UairTrace<
    'static,
    crypto_primitives::crypto_bigint_int::Int<N>,
    crypto_primitives::crypto_bigint_int::Int<N>,
    D,
> {
    type Cell<const N: usize> = crypto_primitives::crypto_bigint_int::Int<N>;
    let int = columns
        .into_iter()
        .map(|col| {
            let evals = col
                .into_iter()
                .map(|limbs| {
                    let mut words = [0u64; N];
                    words[..limbs.len()].copy_from_slice(&limbs);
                    Cell::<N>::from_words(words)
                })
                .collect::<Vec<_>>();
            DenseMultilinearExtension::from_evaluations_vec(num_vars, evals, Cell::<N>::from(0i64))
        })
        .collect::<Vec<_>>();

    UairTrace {
        binary_poly: std::borrow::Cow::Owned(vec![]),
        arbitrary_poly: std::borrow::Cow::Owned(vec![]),
        int: std::borrow::Cow::Owned(int),
    }
}
