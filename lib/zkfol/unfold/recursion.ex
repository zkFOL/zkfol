defmodule Zkfol.Unfold.Recursion do
  @moduledoc """
  I make the recursive calls of the root read the previous column.

  I only do this when every clause of the root calls the root at most once and no other
  relation calls it. The calls then run one after another, so they fit on consecutive
  columns.

  ### Public API

  - `linear/1`: rewrite the root's calls to itself in an unfolded program.
  """

  alias Zkfol.Unfold
  alias Zkfol.Unfold.{Call, Clause}

  @doc "I rewrite the root's calls to itself."
  @spec linear(Unfold.program()) :: Unfold.program()
  def linear(program = [{root, clauses} | members]) do
    other_clauses = Enum.flat_map(members, fn {_key, clauses} -> clauses end)
    linear? = Enum.all?(clauses, &(count(&1, root) <= 1))
    called_elsewhere? = Enum.any?(other_clauses, &(count(&1, root) > 0))

    if linear? and not called_elsewhere? do
      [{root, Enum.map(clauses, &back(&1, root))} | members]
    else
      program
    end
  end

  @spec count(Clause.t(), Unfold.key()) :: non_neg_integer()
  defp count(%Clause{calls: calls}, root) do
    Enum.count(calls, &(&1.member == root))
  end

  @spec back(Clause.t(), Unfold.key()) :: Clause.t()
  defp back(clause = %Clause{calls: calls}, root) do
    %{clause | calls: Enum.map(calls, &back_call(&1, root))}
  end

  @spec back_call(Call.t(), Unfold.key()) :: Call.t()
  defp back_call(call = %Call{member: root}, root), do: %{call | at: :back}
  defp back_call(call, _root), do: call
end
