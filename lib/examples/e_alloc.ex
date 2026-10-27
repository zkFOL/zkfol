defmodule Examples.EAlloc do
  @moduledoc "I am the linker's evidence: named predicates resolve to the regions' rows."

  use ExExample
  use Zkfol

  import ExUnit.Assertions

  alias Zkfol.Al
  alias Zkfol.Alloc
  alias Zkfol.Interpretation
  alias Zkfol.Lay
  alias Zkfol.Phi
  alias Zkfol.Prover

  defrel held(0, 0)

  defrel held(n, value) do
    n1 = n - 1
    held(n1, previous)
    value = previous + n
  end

  defrel delegated(n, value) do
    held(n, value)
  end

  defrel shifted(n, value) do
    n + 1 = n1
    held(n1, value)
  end

  defrel choose(0) do
    nth(1, [1], 2)
  end

  defrel choose(1)

  defrel impossible_after(n, value) do
    blocked = unknown * []
    held(n, value)
    1 = 2
  end

  defrel impossible_before(n, value) do
    1 = 2
    blocked = unknown * []
    held(n, value)
  end

  defrel sum(a, b, c) do
    c = a + b
  end

  defrel erased(a, z) do
    z = 0 * a
  end

  @doc "An impossible lookup clause does not prevent another clause from answering."
  @spec a_dead_lookup_clause() :: Prover.Report.t()
  example a_dead_lookup_clause do
    {:ok, derivation} = Al.derived(choose(), [1])
    {:ok, pred, alloc} = Phi.compile(choose(), nil, [1])
    witness = derivation |> Lay.of(alloc) |> Lay.witness()
    assert {:ok, report, _id} = Prover.prove(Alloc.link(pred, alloc), witness)
    assert {:error, {:no_answer, _}} = Al.derived(choose(), [0])
    report
  end

  @doc "Private scalars share one predicate, directly or through a call; a wrong sum is refused."
  @spec scalar_parameters_share_one_predicate() :: [Prover.Report.t()]
  example scalar_parameters_share_one_predicate do
    reports =
      Enum.flat_map(
        [
          {sum(), [[3, 4, 7], [8, 5, 13]]},
          {delegated(), [[8, 36], [9, 45]]},
          {shifted(), [[0, 1], [1, 3], [2, 6]]}
        ],
        fn {rel, answers} ->
          {:ok, pred, alloc} = Phi.compile(rel)

          for args <- answers do
            assert {:ok, ^pred, ^alloc} = Phi.compile(rel, nil, args)
            {:ok, derivation} = Al.derived(rel, args)
            lay = Lay.of(derivation, alloc)
            witness = Lay.witness(lay)
            {:ok, claims} = Lay.claims(lay, [1])

            assert {:ok, report = %Prover.Report{}, _id} =
                     Prover.prove(Alloc.link(pred, alloc), witness, claims: claims)

            report
          end
        end
      )

    {:ok, pred, alloc} = Phi.compile(sum())
    fact = {:sum, [8, 5, 14]}
    derivation = %Zkfol.Derivation{facts: [fact], clauses: [{fact, 0}]}
    forged = derivation |> Lay.of(alloc) |> Lay.witness()
    assert {:error, _refusal} = Prover.prove(Alloc.link(pred, alloc), forged)
    reports
  end

  @doc "An operand erased by arithmetic owns no row; its private value does not affect the proof."
  @spec an_erased_operand_needs_no_row() :: [Prover.Report.t()]
  example an_erased_operand_needs_no_row do
    {:ok, pred, alloc} = Phi.compile(erased())
    assert [%Alloc.Slot{allocation: :none} | _rest] = Alloc.root(alloc).slots

    for value <- [3, 99] do
      {:ok, derivation} = Al.derived(erased(), [value, 0])
      witness = derivation |> Lay.of(alloc) |> Lay.witness()

      assert {:ok, report = %Prover.Report{}, _id} =
               Prover.prove(Alloc.link(pred, alloc), witness)

      report
    end
  end

  @doc "An impossible clause owns no callee or value rows, wherever the contradiction occurs."
  @spec impossible_clauses_allocate_nothing() :: [Alloc.t()]
  example impossible_clauses_allocate_nothing do
    for rel <- [impossible_after(), impossible_before()] do
      {:ok, pred, alloc} = Phi.compile(rel)
      assert Alloc.refs(alloc) == [{:in, rel.name}]
      linked = Alloc.link(pred, alloc)
      assert Zkfol.Semantics.valid?(linked, Interpretation.new([[0]]))
      refute Zkfol.Semantics.valid?(linked, Interpretation.new([[1]]))
      alloc
    end
  end
end
