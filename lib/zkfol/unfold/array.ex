defmodule Zkfol.Unfold.Array do
  @moduledoc """
  I give a declared array names for its cells, in place of running `array`'s clauses.

  ### Public API

  - `array/5`: the rule for `array(dims, v)` when `dims` are numbers.
  - `banks/1`: the root arrays among the bindings, with their dimensions.
  - `dimensions/1`: the sizes of a nested list.
  """

  alias Zkfol.Lang.{Rel, Term}
  alias Zkfol.Phi.Place
  alias Zkfol.Unfold
  alias Zkfol.Unfold.Bindings

  @doc """
  I bind `v` to new cell names. On a head name of the root the array is laid along the
  columns and its cells are named after that head name.
  """
  @spec array(Rel.t(), [Term.t()], Unfold.env(), [Unfold.step()], Unfold.ctx()) ::
          {[Unfold.item()], Unfold.env(), [Term.goal()]} | nil
  def array(%Rel{phi: {Zkfol.Array, :array}}, [dims, v], env, path, ctx) do
    sizes = Bindings.elements(Bindings.resolve(dims, env), %{})

    if sizes != nil and Enum.all?(sizes, &(is_integer(&1) and &1 >= 0)) do
      value = Bindings.root(v, env)
      root? = ctx.root? and sizes != [] and match?({:var, x} when is_atom(x), value)
      cell = if root?, do: &{:cell, elem(value, 1), &1}, else: &{path, &1}
      cells = Bindings.bracket(Place.cells(sizes, 0, &{:var, cell.(&1)}))
      {env, goals} = declare(value, cells, env)
      {[{:known, value, cells}], env, goals}
    end
  end

  def array(_rel, _args, _env, _path, _ctx), do: nil

  # The array's name is bound to the cells, and what it was bound to before is equated
  # with them.
  @spec declare(Term.t(), Term.t(), Unfold.env()) :: {Unfold.env(), [Term.goal()]}
  defp declare({:var, r}, cells = {:cons, _, _}, env) do
    case env do
      %{^r => ^cells} -> {env, []}
      %{^r => held} -> {Map.put(env, r, cells), [{:eq, held, cells}]}
      _free -> {Map.put(env, r, cells), []}
    end
  end

  defp declare(value, cells, env), do: {env, [{:eq, value, cells}]}

  @doc "I am the root arrays among the bindings, with their dimensions."
  @spec banks(Unfold.env()) :: %{atom() => [non_neg_integer()]}
  def banks(env) do
    for {x, list = {:cons, first, _rest}} <- env,
        match?([{:cell, ^x, _i} | _], Term.names(first)),
        into: %{},
        do: {x, dimensions(list)}
  end

  @doc "I am the sizes of a nested list, outermost first."
  @spec dimensions(Term.t()) :: [non_neg_integer()]
  def dimensions(list = {:cons, first, _rest}),
    do: [length(Bindings.elements(list, %{})) | dimensions(first)]

  def dimensions(_cell), do: []
end
