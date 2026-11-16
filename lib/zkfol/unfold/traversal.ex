defmodule Zkfol.Unfold.Traversal do
  @moduledoc """
  I turn a relation that steps through root arrays into one member that moves a column a
  step, in place of a member call per element.

  A relation traverses when it has an empty base clause and a clause that calls itself
  once, every parameter either stepping one element down a list or passed on unchanged. A
  call starts a traversal when the stepped arguments are root arrays of one length and
  the unchanged ones are constants.

  ### Public API

  - `start/5`: the rule for a call that starts a traversal.
  - `step/5`: the rule for the traversing member's call to itself.
  - `rows/2`: the cell names of the rows a traversing member reads.
  """

  alias Zkfol.Lang.{Rel, Term}
  alias Zkfol.Phi.Place
  alias Zkfol.Unfold
  alias Zkfol.Unfold.{Array, Bindings, Call}

  @typep array :: {:bank, atom(), [non_neg_integer()]}

  @doc "I start a traversal at the column where the arrays' remaining elements begin."
  @spec start(Rel.t(), [Term.t()], Unfold.env(), [Unfold.step()], Unfold.ctx()) ::
          {[Unfold.item()], Unfold.env(), [Term.goal()]} | nil
  def start(%Rel{name: name, clauses: [a, b]}, args, env, path, _ctx) do
    Enum.find_value([{a, b}, {b, a}], fn {{head, body}, {base, rest}} ->
      with [] <- rest,
           [again] <- for({:call, ^name, again} <- body, do: again),
           handed = Enum.map(Enum.zip([base, head, again, args]), &argument(&1, env)),
           false <- nil in handed,
           arrays = [_ | _] <- for({{:bank, v, _inner}, n} <- handed, do: {v, n}),
           true <- arrays == Enum.uniq_by(arrays, &elem(&1, 0)),
           [extent] <- arrays |> Enum.map(&elem(&1, 1)) |> Enum.uniq() do
        handed = Enum.map(handed, &with({array = {:bank, _, _}, _left} <- &1, do: array))
        {[%Call{source: path, member: {name, handed}, args: [], at: {:entry, extent}}], env, []}
      else
        _other -> nil
      end
    end)
  end

  def start(_rel, _args, _env, _path, _ctx), do: nil

  @doc "I continue a traversal one column back, for the member's own clause only."
  @spec step(Rel.t(), [Term.t()], Unfold.env(), [Unfold.step()], Unfold.ctx()) ::
          {[Unfold.item()], Unfold.env(), [Term.goal()]} | nil
  def step(%Rel{name: name}, _args, env, path = [_own], %{key: key = {name, handed}}) do
    if Enum.any?(handed, &match?({:bank, _, _}, &1)),
      do: {[%Call{source: path, member: key, args: [], at: :back}], env, []}
  end

  def step(_rel, _args, _env, _path, _ctx), do: nil

  @doc "I bind the row a traversing member reads at its column to cell names."
  @spec rows([Term.t()], [Unfold.handed()]) :: Unfold.env()
  def rows(head, handed) do
    for {{:cons, {:var, v}, _rest}, {:bank, _array, inner = [_ | _]}} <- Enum.zip(head, handed),
        into: %{},
        do: {v, Bindings.bracket(Place.cells(inner, 0, &{:var, {:row, v, &1}}))}
  end

  # One parameter: its base pattern, its head pattern, what the clause passes to itself,
  # and the caller's argument.
  @spec argument({Term.t(), Term.t(), Term.t(), Term.t()}, Unfold.env()) ::
          {array(), non_neg_integer()} | {:fixed, Term.t()} | nil
  defp argument({nil, {:cons, _head, {:var, tail}}, {:var, tail}, arg}, env),
    do: root_array(arg, env)

  defp argument({{:var, _}, {:var, name}, {:var, name}, arg}, env) do
    value = Bindings.resolve(arg, env)
    if fixed?(value), do: {:fixed, value}
  end

  defp argument(_other, _env), do: nil

  @spec fixed?(Term.t()) :: boolean()
  defp fixed?(q) when is_integer(q), do: true
  defp fixed?({:papply, _p, fixed}), do: Enum.all?(fixed, &fixed?/1)
  defp fixed?(_term), do: false

  # The root array a list is, or is the rest of, and how many elements are left. The
  # list must be the array's own cells; an equal list written with other names is not it.
  @spec root_array(Term.t(), Unfold.env()) :: {array(), non_neg_integer()} | nil
  defp root_array(term, env) do
    with left = [first | _] <- Bindings.elements(term, env),
         [{:cell, array, _i} | _] <- Term.names(first),
         whole = [_ | _] <- Bindings.elements({:var, array}, env),
         true <- List.starts_with?(Enum.reverse(whole), Enum.reverse(left)) do
      {{:bank, array, Array.dimensions(first)}, length(left)}
    else
      _other -> nil
    end
  end
end
