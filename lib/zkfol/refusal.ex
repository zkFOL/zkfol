defmodule Zkfol.Refusal do
  @moduledoc """
  I am the index of every refusal the compiler can make, a refusal being `{reason, detail}`
  and its prose derived here. A refusal's kind says what the caller should do:

  - `:restructure`: the statement's shape is not one I compile; rewrite it.
  - `:out_of_range`: a bound was exceeded; shrink it, or raise the bound.
  - `:false_statement`: the statement is not true; the only kind that is a result.
  - `:transport`: the prover died, timed out, or never answered; retry.
  """

  @typedoc "The values the message needs, and a view can point at."
  @type detail :: map()

  @typedoc "A refusal: what it is, and what it is about."
  @type t :: {reason(), detail()}

  @typedoc "A refusal drawn from `reason` only: `Refusal.t(Refusal.restructure())`."
  @type t(reason) :: {reason, detail()}

  @doc "I hold that no element of `enum` satisfies `bad?`; `refusal` names the first that does."
  @spec refute(Enumerable.t(), (term() -> boolean()), (term() -> t())) :: :ok | {:error, t()}
  def refute(enum, bad?, refusal) do
    case Enum.find(enum, bad?) do
      nil -> :ok
      offender -> {:error, refusal.(offender)}
    end
  end

  @doc "I map each element through `fun`, and the first refusal halts the walk."
  @spec map(Enumerable.t(), (term() -> {:ok, term()} | {:error, t()})) ::
          {:ok, [term()]} | {:error, t()}
  def map(enum, fun) do
    enum
    |> Enum.reduce_while({:ok, []}, fn elem, {:ok, acc} ->
      case fun.(elem) do
        {:ok, value} -> {:cont, {:ok, [value | acc]}}
        refusal -> {:halt, refusal}
      end
    end)
    |> case do
      {:ok, values} -> {:ok, Enum.reverse(values)}
      refusal -> refusal
    end
  end

  @doc "I am `map/2` with the results concatenated, for steps that yield lists."
  @spec flat_map(Enumerable.t(), (term() -> {:ok, [term()]} | {:error, t()})) ::
          {:ok, [term()]} | {:error, t()}
  def flat_map(enum, fun) do
    with {:ok, chunks} <- map(enum, fun), do: {:ok, Enum.concat(chunks)}
  end

  @doc "I read the backend's prose back into a refusal."
  @spec from_backend(String.t()) :: t()
  def from_backend("verifier failed" <> _rest = said), do: {:verifier_rejected, %{said: said}}
  def from_backend(said), do: {:prover_failed, %{said: said}}

  @doc "I read AL's blown-bound sentence into a refusal; its own tuples pass through."
  @spec from_al(term()) :: term()
  def from_al({:error, said}) when is_binary(said), do: {:error, {:heap_exhausted, %{said: said}}}
  def from_al(other), do: other

  @doc "I read `refusal` out as prose, for a human at the end of the line."
  @spec message(t()) :: String.t()
  def message(refusal), do: refusal |> said() |> elem(1)

  @spec said(t()) :: {atom(), String.t()}
  defp said({:not_solved, %{stage: stage}}),
    do:
      {:restructure,
       "the route stopped at #{inspect(stage)}, before the lowering: nothing to prove or emit"}

  defp said({:not_a_recurrence, %{relation: name}}),
    do: {:restructure, "#{name} is not an order-2 linear recurrence"}

  defp said({:no_relations, _detail}),
    do: {:restructure, "the statement carries no relations; supply its witness instead"}

  defp said({:unbound_variable, %{variable: name}}),
    do: {:restructure, "the variable #{name} is not bound by the head or a call"}

  defp said({:unbound_variable, %{goals: goals}}),
    do: {:restructure, "the goals #{inspect(goals)} name a variable no clause binds"}

  defp said({:unbound_variable, %{equation: {a, b}}}),
    do: {:restructure, "the equation #{inspect(a)} = #{inspect(b)} binds no variable"}

  defp said({:relation_not_in_scope, %{relation: name}}),
    do: {:restructure, "the relation #{name} is not in scope"}

  defp said({:read_row_claimed, %{row: row}}),
    do:
      {:restructure,
       "row #{row} is both claimed and part of a composed read; " <>
         "the pointer query binds witness columns only"}

  defp said({:unliftable_term, %{term: term}}),
    do: {:restructure, "no clause lowers the term #{inspect(term)}"}

  defp said({:array_shape, %{dimensions: dimensions}}),
    do:
      {:restructure,
       "array dimensions must be static nonnegative integers: #{inspect(dimensions)}"}

  defp said({:unliftable_count, %{}}),
    do: {:restructure, "the call's count lifts to no frame, and no pointer stands for it"}

  defp said({:symbol_not_allocated, %{symbol: sym}}),
    do: {:restructure, "the bank #{sym} stands on no member"}

  defp said({:head_not_a_column, %{head: head}}),
    do:
      {:restructure,
       "a clause head names its column with a constant or a variable, not #{inspect(head)}"}

  defp said({:arguments_exceed_rows, %{args: args, rows: rows}}),
    do: {:restructure, "#{args} arguments for a relation of #{rows} rows"}

  defp said({:len_needs_a_bound_count, %{}}),
    do: {:restructure, "len is the trace length, which only a bound count names"}

  defp said({:residue, %{answer: answer}}),
    do:
      {:restructure,
       "the search answered with rows still open: #{inspect(answer)}; pin one and ask again"}

  defp said({:publicity_is_the_acts, %{claims: claims}}),
    do:
      {:restructure,
       "publicity is the act's, and the statement already claims #{inspect(claims)}"}

  defp said({:precedes_base_case, %{n: n, base: base}}),
    do: {:out_of_range, "n=#{n} precedes the base case index #{base}"}

  defp said({:read_row_outside_witness, %{row: row}}),
    do: {:out_of_range, "the composed read names row #{row} outside the witness"}

  defp said({:pointer_row_outside_matrix, %{row: row}}),
    do:
      {:out_of_range, "pointer row #{row} leaves the matrix: a composed read needs 1 <= A <= len"}

  defp said({:claim_outside_witness, %{claim: name, row: row, column: x}}),
    do: {:out_of_range, "claim #{inspect(name)} names cell (#{row}, #{x}) outside the witness"}

  defp said({:beyond_the_rows, %{relation: name}}),
    do: {:out_of_range, "a claim on #{name} reaches beyond the rows it stands on"}

  defp said({:beyond_the_rows, %{sequence: seq}}),
    do: {:out_of_range, "a claim on the sequence #{seq} reaches beyond the cells it holds"}

  defp said({:selection_changes_claim, %{claim: name, row: row, column: x}}),
    do:
      {:restructure,
       "the unconditional selection would change #{name} at (#{row}, #{x}); " <>
         "this opening needs a conditional lookup"}

  defp said({:selection_outside_trace, %{cell: cell, column: x}}),
    do: {:out_of_range, "no selection names #{inspect(cell)} at column #{x}: outside the trace"}

  defp said({:witness_value_negative, %{value: value}}),
    do: {:out_of_range, "witness value #{value} is negative; cells carry no sign"}

  defp said({:heap_exhausted, %{said: said}}), do: {:out_of_range, said}

  defp said({:unresolved_within_budget, %{reductions: n}}),
    do: {:out_of_range, "no verdict within #{n} reductions; CLP or a bound count may reach it"}

  defp said({:value_exceeds_cell, %{value: value}}),
    do: {:out_of_range, "witness value #{value} does not fit 7040-bit cells"}

  defp said({:constant_exceeds_cell, %{constant: k}}),
    do: {:out_of_range, "predicate constant #{k} does not fit the program's i64 cells"}

  defp said({:witness_unsatisfies_schedule, %{column: x}}),
    do: {:false_statement, "the witness does not satisfy the scheduled statement at column #{x}"}

  defp said({:verifier_rejected, %{said: said}}), do: {:false_statement, said}

  defp said({:no_answer, %{relation: name}}),
    do:
      {:false_statement, "the question found no answer: nothing derives #{name} at those values"}

  defp said({:no_answer, %{}}),
    do: {:false_statement, "the question found no answer: nothing derives those values"}

  defp said({:send_failed, %{reason: reason}}),
    do: {:transport, "the send failed: " <> clip(reason)}

  defp said({:prover_timeout, %{intent: id}}),
    do: {:transport, "the prover did not settle intent #{id} in time"}

  defp said({:prover_died, _detail}), do: {:transport, "the prover died before the verdict"}
  defp said({:prover_failed, %{said: said}}), do: {:transport, said}

  # The index is read off said/1's clauses while the module still compiles.
  {:v1, :defp, _meta, clauses} = Module.get_definition(__MODULE__, {:said, 1})

  @index Map.new(
           for {_meta, [{reason, _detail}], _guards, {kind, _prose}} <- clauses,
               do: {reason, kind}
         )

  @union fn reasons -> Enum.reduce(reasons, &{:|, [], [&1, &2]}) end

  @typedoc "Every refusal the compiler can make."
  @type reason :: unquote(@union.(Map.keys(@index)))

  for {kind, reasons} <- Enum.group_by(@index, &elem(&1, 1), &elem(&1, 0)) do
    @typedoc "The refusals that ask the caller to #{kind}."
    @type unquote({kind, [], nil}) :: unquote(@union.(reasons))
  end

  @doc "I am every reason the index knows."
  @spec reasons() :: [reason()]
  def reasons, do: Map.keys(@index)

  @clip 120

  @spec clip(term()) :: String.t()
  defp clip(term) when is_binary(term), do: String.slice(term, 0, @clip)
  defp clip(term), do: term |> inspect(limit: 8) |> String.slice(0, @clip)
end
