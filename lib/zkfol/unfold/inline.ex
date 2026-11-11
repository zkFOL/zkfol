defmodule Zkfol.Unfold.Inline do
  @moduledoc """
  I replace a call by the body of one clause of its relation: the head names become the
  call's arguments and the clause's other names carry the call they came through.

  ### Public API

  - `native/5`: the rule for a relation the solver answers natively. Its derivation holds
    no call to point at, so the clause has to be unfolded.
  - `only_clause/5`: the rule for a call that only one clause can match.
  - `rename/2`: apply a function to every variable of a term or goal.
  """

  alias Zkfol.Ast
  alias Zkfol.Lang.{Rel, Term}
  alias Zkfol.Unfold
  alias Zkfol.Unfold.Bindings

  @depth 64

  @typep clause :: {[Term.t()], [Term.goal()]}

  @doc "I unfold the one clause of a relation the solver answers natively."
  @spec native(Rel.t(), [Term.t()], Unfold.env(), [Unfold.step()], Unfold.ctx()) ::
          {[Unfold.item()], Unfold.env(), [Term.goal()]} | nil
  def native(%Rel{al: al, clauses: [clause]}, args, env, path, _ctx) when al != nil,
    do: {[], env, unfolded(clause, args, path)}

  def native(_rel, _args, _env, _path, _ctx), do: nil

  @doc "I unfold a call when only one clause's head, equations and guards fit it."
  @spec only_clause(Rel.t(), [Term.t()], Unfold.env(), [Unfold.step()], Unfold.ctx()) ::
          {[Unfold.item()], Unfold.env(), [Term.goal()]} | nil
  def only_clause(rel, args, env, path, ctx) do
    fitting =
      for clause <- rel.clauses,
          goals = unfolded(clause, args, path),
          consistent?(goals, env, path, ctx),
          do: goals

    with true <- length(path) <= @depth, [goals] <- fitting do
      {[], env, goals}
    else
      _none_or_several -> nil
    end
  end

  @doc "I apply `fun` to every variable of a term or goal."
  @spec rename(term(), (Term.t() -> Term.t())) :: term()
  def rename({:var, _} = var, fun), do: fun.(var)

  def rename({tag, a, b}, fun) when tag in [:eq, :add, :mul, :cons],
    do: {tag, rename(a, fun), rename(b, fun)}

  def rename({:call, q, args}, fun), do: {:call, rename(q, fun), rename(args, fun)}
  def rename({:papply, p, args}, fun), do: {:papply, p, rename(args, fun)}
  def rename(terms, fun) when is_list(terms), do: Enum.map(terms, &rename(&1, fun))
  def rename(leaf, _fun), do: leaf

  # The goals a clause becomes at a call: the equations its head adds, then its body.
  @spec unfolded(clause(), [Term.t()], [Unfold.step()]) :: [Term.goal()]
  defp unfolded({head, body}, args, path) do
    qualify = fn {:var, v} -> {:var, {path, v}} end
    bind_head(Enum.zip(rename(head, qualify), args), [], rename(body, qualify), path)
  end

  # A head name is replaced by its argument in the body. Any other head pattern, and a
  # head name that was already replaced, is equated with its argument.
  @spec bind_head([{Term.t(), Term.t()}], [Term.goal()], [Term.goal()], [Unfold.step()]) ::
          [Term.goal()]
  defp bind_head([], equations, body, _path), do: Enum.reverse(equations, body)

  defp bind_head([{{:var, v = {path, _name}}, arg} | rest], equations, body, path) do
    replace = &rename(&1, fn term -> if term == {:var, v}, do: arg, else: term end)
    rest = for {pattern, other} <- rest, do: {replace.(pattern), other}
    bind_head(rest, equations, replace.(body), path)
  end

  defp bind_head([{pattern, arg} | rest], equations, body, path),
    do: bind_head(rest, [{:eq, arg, pattern} | equations], body, path)

  @spec consistent?([Term.goal()], Unfold.env(), [Unfold.step()], Unfold.ctx()) :: boolean()
  defp consistent?(goals, env, path, ctx) do
    goals
    |> Enum.with_index()
    |> Enum.reduce(env, fn
      _goal, nil -> nil
      {{:eq, a, b}, _k}, env -> Bindings.unify(a, b, env)
      {{:call, q, args}, k}, env -> guard(q, args, env, path ++ [{nil, k}], ctx)
    end) != nil
  end

  # A relation the solver answers natively is decided here when its arguments are numbers;
  # otherwise it is assumed to hold.
  @spec guard(term(), [Term.t()], Unfold.env(), [Unfold.step()], Unfold.ctx()) ::
          Unfold.env() | nil
  defp guard(q, args, env, path, ctx) do
    {rel, args} = Bindings.callee(q, args, env, ctx.scope)

    case {rel.al, rel.phi, rel.clauses, Enum.map(args, &Bindings.resolve(&1, env))} do
      {nil, _phi, _clauses, _args} ->
        env

      {_al, {Ast, :natural}, _clauses, [q]} when is_integer(q) and q < 0 ->
        nil

      {_al, nil, [clause], _args} ->
        if(consistent?(unfolded(clause, args, path), env, path, ctx), do: env)

      _unknown ->
        env
    end
  end
end
