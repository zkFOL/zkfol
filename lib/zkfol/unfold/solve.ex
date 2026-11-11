defmodule Zkfol.Unfold.Solve do
  @moduledoc """
  I turn what unfolding left of a clause into the `Clause` the lowering reads.

  A stored name keeps its name and what it is bound to becomes an equation. A name bound
  to a sum is the sum's one unknown solved for. Any other bound name is replaced by its
  value. A number that is left with no place takes a cell of its own.

  ### Public API

  - `clause/3`: the clause for a head, the items unfolding left and the bindings.
  """

  alias Zkfol.Ast
  alias Zkfol.Lang.Term
  alias Zkfol.Unfold
  alias Zkfol.Unfold.{Array, Bindings, Call, Clause, Primitive}

  @typep equation :: {Term.t(), Term.t()}

  @doc "I am the clause for `head`, the items unfolding left and the bindings."
  @spec clause([Term.t()], [Unfold.item()], Unfold.env()) :: Clause.t()
  def clause(head, items, env) do
    calls = for call = %Call{} <- items, do: call

    unsolved =
      for {:eq, a, b} <- items,
          Bindings.resolve(a, env) != Bindings.resolve(b, env),
          uniq: true,
          do: {a, b}

    # A name bound to a sum goes back to being an equation, so `solve_sums/3` can choose
    # which of its names to solve for.
    {sums, bound} = Map.split_with(env, &match?({_v, {op, _, _}} when op in [:add, :mul], &1))
    matched = matched(calls, bound)
    unsolved = unsolved ++ for({v, sum} <- sums, do: {{:var, v}, sum})
    {bound, unsolved} = solve_sums(bound, unsolved, matched)

    subst = &substitute(&1, bound, matched)

    stored =
      for {v, term} <- Enum.sort(bound), readable?(v, matched), do: {{:var, v}, subst.(term)}

    calls = for call <- calls, do: %{call | args: Enum.map(call.args, subst)}
    equations = for {a, b} <- unsolved, do: {subst.(a), subst.(b)}
    primitives = for prim = %Primitive{} <- items, do: %{prim | args: Enum.map(prim.args, subst)}

    # A number that nothing else places takes a cell of its own.
    numbers =
      Enum.flat_map(primitives, &Term.names(&1.args)) ++
        Enum.flat_map(calls, &summed(&1.args)) ++
        Enum.flat_map(stored ++ equations, &summed(Tuple.to_list(&1)))

    %Clause{
      head: head,
      banks: Array.banks(env),
      own_cells: numbers |> Enum.uniq() |> Enum.reject(&readable?(&1, matched)),
      calls: calls,
      equations: Enum.sort_by(stored, &equation_order/1) ++ equations,
      primitives: primitives
    }
  end

  # Equations that open a list come first and sums last, so the names inside a list have
  # values before a sum reads them.
  @spec equation_order(equation()) :: 0..2
  defp equation_order({_name, term}) do
    cond do
      summed(term) != [] -> 2
      match?({:cons, _, _}, term) -> 0
      true -> 1
    end
  end

  # The names a term adds or multiplies.
  @spec summed(term()) :: [Unfold.name()]
  defp summed({op, a, b}) when op in [:add, :mul], do: Term.names([a, b])
  defp summed(terms) when is_list(terms), do: Enum.flat_map(terms, &summed/1)
  defp summed({:cons, h, t}), do: summed([h, t])
  defp summed({:papply, _p, fixed}), do: summed(fixed)
  defp summed(_leaf), do: []

  # The free names the lowering gives a value by matching: the arguments of a pointer
  # call and the elements of a stored name's list.
  @spec matched([Call.t()], Unfold.env()) :: MapSet.t(Unfold.name())
  defp matched(calls, env) do
    arguments = for %Call{at: :pointer, args: args} <- calls, arg <- args, do: arg
    lists = for {v, list = {:cons, _, _}} <- env, Bindings.stored?(v), do: list
    MapSet.new(Enum.flat_map(arguments ++ lists, &pattern_names(&1, env)))
  end

  @spec pattern_names(Term.t(), Unfold.env()) :: [Unfold.name()]
  defp pattern_names(var = {:var, _}, env) do
    {:var, r} = Bindings.root(var, env)

    cond do
      Bindings.stored?(r) -> []
      match?(%{^r => {:cons, _, _}}, env) -> pattern_names(env[r], env)
      is_map_key(env, r) -> []
      true -> [r]
    end
  end

  defp pattern_names({:cons, h, t}, env), do: pattern_names(h, env) ++ pattern_names(t, env)
  defp pattern_names(_other, _env), do: []

  @spec readable?(Unfold.name(), MapSet.t(Unfold.name())) :: boolean()
  defp readable?(name, matched), do: Bindings.stored?(name) or name in matched

  # n = m + q  =>  m = n - q. An equation with exactly one name the lowering cannot read
  # is solved for that name when it is a summand: a guard's slack, or a name defined by a
  # sum.
  @spec solve_sums(Unfold.env(), [equation()], MapSet.t(Unfold.name())) ::
          {Unfold.env(), [equation()]}
  defp solve_sums(env, equations, matched) do
    subst = &substitute(&1, env, matched)

    solved =
      Enum.find_value(equations, fn equation = {a, b} ->
        {a, b} = {subst.(a), subst.(b)}
        with {m, v} <- solve_sum(a, b, matched) || solve_sum(b, a, matched), do: {equation, m, v}
      end)

    case solved do
      {equation, m, v} -> solve_sums(Map.put(env, m, v), equations -- [equation], matched)
      nil -> {env, equations}
    end
  end

  @spec solve_sum(Term.t(), Term.t(), MapSet.t(Unfold.name())) ::
          {Unfold.name(), Term.t()} | nil
  defp solve_sum(sum, other, matched) do
    summands = summands(sum)

    with [m] <- Enum.reject(Term.names([sum, other]), &readable?(&1, matched)),
         true <- {:var, m} in summands do
      {m, Ast.sub(other, Enum.reduce(summands -- [{:var, m}], 0, &Ast.add(&2, &1)))}
    else
      _other -> nil
    end
  end

  @spec summands(Term.t()) :: [Term.t()]
  defp summands({:add, a, b}), do: summands(a) ++ summands(b)
  defp summands(term), do: [term]

  # Every bound name is replaced by its value, except the names the lowering reads.
  @spec substitute(Term.t(), Unfold.env(), MapSet.t(Unfold.name())) :: Term.t()
  defp substitute(var = {:var, _}, env, matched) do
    {:var, r} = Bindings.root(var, env)

    if is_map_key(env, r) and not readable?(r, matched),
      do: substitute(env[r], env, matched),
      else: {:var, r}
  end

  defp substitute({op, a, b}, env, matched) when op in [:add, :mul],
    do: apply(Ast, op, [substitute(a, env, matched), substitute(b, env, matched)])

  defp substitute({:cons, h, t}, env, matched),
    do: {:cons, substitute(h, env, matched), substitute(t, env, matched)}

  defp substitute({:papply, p, fixed}, env, matched),
    do: {:papply, p, Enum.map(fixed, &substitute(&1, env, matched))}

  defp substitute(term, _env, _matched), do: term
end
