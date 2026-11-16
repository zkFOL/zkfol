defmodule Zkfol.Unfold.Bindings do
  @moduledoc """
  I am what unfolding knows about names: each bound name with the term it equals.

      v = t              v is bound to t                v a free name
      [h | t] = [i | u]  h = i and t = u
      q = r              holds or not                   both numbers
      v + q = r          v is bound to r - q            q and r numbers

  ### Public API

  - `unify/3`: the bindings after an equation, or nil when it cannot hold.
  - `resolve/2`, `root/2`, `elements/2`: read a term through the bindings.
  - `callee/4`: the relation a call names.
  - `stored?/1`: whether a name has a cell of its own.
  - `bracket/1`: a list of terms as a list term.
  """

  alias Zkfol.Ast
  alias Zkfol.Lang.{Rel, Term}
  alias Zkfol.Unfold

  @doc "I am the bindings after `a = b`, or nil when the two cannot be equal."
  @spec unify(Term.t(), Term.t(), Unfold.env()) :: Unfold.env() | nil
  def unify(a, b, env) do
    case {deref(a, env), deref(b, env)} do
      {same, same} ->
        env

      {{:var, v}, {:var, w}} ->
        if rank(v) > rank(w), do: Map.put(env, w, {:var, v}), else: Map.put(env, v, {:var, w})

      {{:var, v}, _value} ->
        bind(v, root(b, env), env)

      {_value, {:var, w}} ->
        bind(w, root(a, env), env)

      {{:cons, h, t}, {:cons, i, u}} ->
        with env = %{} <- unify(h, i, env), do: unify(t, u, env)

      {{:add, {:var, v}, q}, r} when is_integer(q) and is_integer(r) ->
        Map.put(env, v, r - q)

      {r, {:add, {:var, v}, q}} when is_integer(q) and is_integer(r) ->
        Map.put(env, v, r - q)

      {x, y} ->
        if clash?(x, y), do: nil, else: env
    end
  end

  @doc "I am `term` with bound names replaced by their values and constants folded."
  @spec resolve(Term.t(), Unfold.env()) :: Term.t()
  def resolve({:var, v}, env) when is_map_key(env, v), do: resolve(env[v], env)
  def resolve({:add, a, b}, env), do: Ast.add(resolve(a, env), resolve(b, env))
  def resolve({:mul, a, b}, env), do: Ast.mul(resolve(a, env), resolve(b, env))
  def resolve({:cons, h, t}, env), do: {:cons, resolve(h, env), resolve(t, env)}
  def resolve({:papply, p, fixed}, env), do: {:papply, p, Enum.map(fixed, &resolve(&1, env))}
  def resolve(term, _env), do: term

  @doc "I am the last name of a chain of names bound to names."
  @spec root(Term.t(), Unfold.env()) :: Term.t()
  def root(var = {:var, v}, env) do
    case env do
      %{^v => next = {:var, _}} -> root(next, env)
      _value_or_free -> var
    end
  end

  def root(term, _env), do: term

  @doc "I am the elements of a list as written, following bound names; nil when it is not closed."
  @spec elements(Term.t(), Unfold.env()) :: [Term.t()] | nil
  def elements({:var, v}, env) when is_map_key(env, v), do: elements(env[v], env)

  def elements({:cons, h, t}, env),
    do: with(rest when is_list(rest) <- elements(t, env), do: [h | rest])

  def elements(nil, _env), do: []
  def elements(_open, _env), do: nil

  @doc "I am a nested list of terms as a list term."
  @spec bracket(term()) :: Term.t()
  def bracket(terms) when is_list(terms), do: List.foldr(terms, nil, &{:cons, bracket(&1), &2})
  def bracket(term), do: term

  @doc "I am the relation a call names; a passed relation's fixed arguments go first."
  @spec callee(term(), [Term.t()], Unfold.env(), %{atom() => Rel.t()}) :: {Rel.t(), [Term.t()]}
  def callee(q, args, env, scope) do
    case resolve(q, env) do
      {:papply, p, fixed} -> {Map.fetch!(scope, Rel.name(p)), fixed ++ args}
      {:var, _unbound} -> throw({:refused, {:unbound_variable, %{goals: [{:call, q, args}]}}})
      named -> {Map.fetch!(scope, Rel.name(named)), args}
    end
  end

  @doc "I say whether a name has a cell of its own: a head name, or a cell or row name."
  @spec stored?(Unfold.name()) :: boolean()
  def stored?(name), do: is_atom(name) or tuple_size(name) == 3

  # `resolve/2` at the top of the term only: a list keeps its elements as written.
  @spec deref(Term.t(), Unfold.env()) :: Term.t()
  defp deref({:var, v}, env) when is_map_key(env, v), do: deref(env[v], env)
  defp deref(sum = {op, _, _}, env) when op in [:add, :mul], do: resolve(sum, env)
  defp deref(term, _env), do: term

  # Of two names for one value the lower-ranked is bound to the other: a stored name is
  # never replaced by a source name, nor a source name by a cell of an unstored array.
  @spec rank(Unfold.name()) :: 0..2
  defp rank(name) do
    cond do
      stored?(name) -> 2
      is_atom(elem(name, 1)) -> 1
      true -> 0
    end
  end

  # A free name v takes a value. When the value is held by a lower-ranked name r, v
  # holds it instead and r is bound to v.
  @spec bind(Unfold.name(), Term.t(), Unfold.env()) :: Unfold.env()
  defp bind(v, {:var, r}, env) do
    if rank(v) > rank(r),
      do: env |> Map.put(v, Map.fetch!(env, r)) |> Map.put(r, {:var, v}),
      else: Map.put(env, v, {:var, r})
  end

  defp bind(v, term, env), do: Map.put(env, v, term)

  @spec clash?(Term.t(), Term.t()) :: boolean()
  defp clash?(a, b) when is_integer(a) and is_integer(b), do: true
  defp clash?(a, b), do: shape(a) != nil and shape(b) != nil and shape(a) != shape(b)

  @spec shape(Term.t()) :: :number | :empty | :list | nil
  defp shape(q) when is_integer(q), do: :number
  defp shape(nil), do: :empty
  defp shape({:cons, _, _}), do: :list
  defp shape(_other), do: nil
end
