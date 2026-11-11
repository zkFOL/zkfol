defmodule Zkfol.Unfold.Lookup do
  @moduledoc """
  I give `nth`, `all_distinct` and `permutation` their own constraints where the source
  states the list, in place of running their clauses.

  ### Public API

  - `nth/5`: the rule for a read at an index.
  - `lookup/5`: the rule for `all_distinct` and `permutation` over trace cells.
  """

  alias Zkfol.Ast
  alias Zkfol.Lang.{Rel, Term}
  alias Zkfol.Unfold
  alias Zkfol.Unfold.{Bindings, Primitive}

  @doc "I read a closed list of numbers at an index as one constraint."
  @spec nth(Rel.t(), [Term.t()], Unfold.env(), [Unfold.step()], Unfold.ctx()) ::
          {[Unfold.item()], Unfold.env(), [Term.goal()]} | nil
  def nth(%Rel{phi: {Ast, :nth}}, [i, list, v], env, _path, _ctx) do
    cells = Bindings.elements(list, env)

    if cells != nil and not Enum.any?(cells, &Term.sequence?(Bindings.resolve(&1, env))),
      do: {[%Primitive{op: :nth, args: [i, Bindings.bracket(cells), v]}], env, []}
  end

  def nth(_rel, _args, _env, _path, _ctx), do: nil

  @doc """
  I turn `all_distinct` and `permutation` into a lookup. A lookup only proves over trace
  cells: the cells of a root array or of a traversed row.
  """
  @spec lookup(Rel.t(), [Term.t()], Unfold.env(), [Unfold.step()], Unfold.ctx()) ::
          {[Unfold.item()], Unfold.env(), [Term.goal()]} | nil
  def lookup(%Rel{phi: {Ast, :distinct}}, [list], env, _path, _ctx),
    do: over_cells(:distinct, [], list, env)

  def lookup(%Rel{phi: {Ast, :permutation}}, [n, list], env, _path, _ctx) do
    case Bindings.resolve(n, env) do
      count when is_integer(count) -> over_cells(:permutation, [count], list, env)
      _unknown -> nil
    end
  end

  def lookup(_rel, _args, _env, _path, _ctx), do: nil

  @spec over_cells(atom(), [Term.t()], Term.t(), Unfold.env()) ::
          {[Unfold.item()], Unfold.env(), [Term.goal()]} | nil
  defp over_cells(op, fixed, list, env) do
    with cells when is_list(cells) <- Bindings.elements(list, env),
         cells = Enum.map(cells, &Bindings.root(&1, env)),
         true <- Enum.all?(cells, &match?({:var, {tag, _, _}} when tag in [:cell, :row], &1)) do
      {[%Primitive{op: op, args: fixed ++ [Bindings.bracket(cells)]}], env, []}
    else
      _other -> nil
    end
  end
end
