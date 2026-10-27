defmodule Examples.ERefusal do
  @moduledoc "I am the index's evidence: every reason it knows reads out as prose."

  use ExExample

  import ExUnit.Assertions

  alias Zkfol.Refusal

  @spec every_reason_reads_as_prose() :: [String.t()]
  example every_reason_reads_as_prose do
    said = for refusal <- detailed(), do: Refusal.message(refusal)

    assert Enum.sort(Refusal.reasons()) ==
             detailed() |> Enum.map(&elem(&1, 0)) |> Enum.uniq() |> Enum.sort()

    assert Enum.all?(said, &(is_binary(&1) and &1 != ""))
    said
  end

  @doc "One refusal per clause of the index, detailed as its producer details it."
  @spec detailed() :: [Refusal.t()]
  def detailed do
    [
      {:arguments_exceed_rows, %{args: 3, rows: 2}},
      {:beyond_the_rows, %{relation: :fib}},
      {:beyond_the_rows, %{sequence: :xs}},
      {:claim_outside_witness, %{claim: "fib.v", row: 9, column: 1}},
      {:constant_exceeds_cell, %{constant: Integer.pow(2, 63)}},
      {:head_not_a_column, %{head: {:add, 1, 1}}},
      {:heap_exhausted, %{said: "the derivation exceeded 256000000 heap words"}},
      {:no_answer, %{relation: :fib}},
      {:no_answer, %{}},
      {:no_relations, %{}},
      {:not_a_recurrence, %{relation: :fib}},
      {:pointer_row_outside_matrix, %{row: 9}},
      {:precedes_base_case, %{n: 0, base: 1}},
      {:prover_died, %{}},
      {:prover_failed, %{said: "the prover panicked"}},
      {:prover_timeout, %{intent: 7}},
      {:publicity_is_the_acts, %{claims: [{"fib.v", 1, 8}]}},
      {:not_solved, %{stage: Zkfol.Derivation}},
      {:read_row_claimed, %{row: 1}},
      {:read_row_outside_witness, %{row: 9}},
      {:relation_not_in_scope, %{relation: :nowhere}},
      {:residue, %{answer: [1, {:var, :x}]}},
      {:selection_changes_claim, %{claim: "accepts.cells", row: 2, column: 1}},
      {:selection_outside_trace, %{cell: {:cell, 2}, column: 9}},
      {:send_failed, %{reason: :nope}},
      {:symbol_not_allocated, %{symbol: :xs}},
      {:unbound_variable, %{variable: :v}},
      {:unbound_variable, %{goals: [{:call, :nth, [1, {:var, :xs}, {:var, :v}]}]}},
      {:unbound_variable, %{equation: {{:var, :a}, 1}}},
      {:unliftable_count, %{}},
      {:unroll_budget, %{relation: :f}},
      {:unliftable_term, %{term: {:papply, :f, []}}},
      {:unresolved_within_budget, %{reductions: 100_000}},
      {:value_exceeds_cell, %{value: Integer.pow(2, 7040)}},
      {:verifier_rejected, %{said: "verifier failed: ProofRejected"}},
      {:witness_unsatisfies_schedule, %{column: 3}},
      {:witness_value_negative, %{value: -1}}
    ]
  end
end
