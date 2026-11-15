defmodule Zkfol.Unfold do
  @moduledoc """
  I rewrite a program before it is lowered: I unfold the clauses of every relation the
  root reaches and return what is left of each as a `Clause`.

  An equation is unified as it is met. A call is rewritten by the first of `call_rules/0`
  that applies. The `:needed` rules compile every program on their own; a `:cheaper` rule
  only makes the proof smaller.

  ### Public API

  - `program/2`: the members a root needs, each with its unfolded clauses.
  - `call_rules/0`: the rules for a call, in the order they are tried.
  """

  use TypedStruct

  alias Zkfol.Ast
  alias Zkfol.Lang.{Rel, Term}
  alias Zkfol.Unfold.{Array, Bindings, Inline, Lookup, Recursion, Solve, Traversal}

  @typedoc "A call in a body: the relation and its position among the body's calls to it."
  @type step :: {atom() | nil, non_neg_integer()}

  @typedoc """
  A variable name. Head names stay atoms; any other name carries the calls it was unfolded
  through. Cells of a root array and cells of a traversed row are named after the head
  name they belong to.
  """
  @type name ::
          atom()
          | {[step()], atom() | non_neg_integer()}
          | {:cell | :row, atom(), non_neg_integer()}

  @typedoc """
  What a member's parameter is specialised to: a passed relation with n fixed arguments,
  a root array the member traverses, or a constant.
  """
  @type handed ::
          nil
          | {:relation, atom(), non_neg_integer()}
          | {:bank, atom(), [non_neg_integer()]}
          | {:fixed, Term.t()}

  @typedoc "A member: a relation and what each of its parameters is specialised to."
  @type key :: {atom(), [handed()]}

  @typedoc """
  Where a call finds its member: through a pointer cell, at the column a traversal starts,
  or one column back inside a traversal.
  """
  @type at :: :pointer | {:entry, non_neg_integer()} | :back

  typedstruct module: Call, enforce: true do
    @moduledoc """
    I am a call to a member. `source` is the calls it was unfolded through and `args` the
    arguments it passes.
    """
    field(:source, [Zkfol.Unfold.step()])
    field(:member, Zkfol.Unfold.key())
    field(:args, [Zkfol.Lang.Term.t()])
    field(:at, Zkfol.Unfold.at())
  end

  typedstruct module: Primitive, enforce: true do
    @moduledoc "I am a primitive constraint over numbers and lists of cells."
    field(:op, :natural | :nth | :distinct | :permutation)
    field(:args, [Zkfol.Lang.Term.t()])
  end

  typedstruct module: Clause, enforce: true do
    @moduledoc """
    I am an unfolded clause. `banks` are the root arrays it declares and `own_cells` the
    names that need a cell of their own. The lowering reads the calls, then the equations,
    then the primitives.
    """
    field(:head, [Zkfol.Lang.Term.t()])
    field(:banks, %{atom() => [non_neg_integer()]})
    field(:own_cells, [Zkfol.Unfold.name()])
    field(:calls, [Zkfol.Unfold.Call.t()])
    field(:equations, [{Zkfol.Lang.Term.t(), Zkfol.Lang.Term.t()}])
    field(:primitives, [Zkfol.Unfold.Primitive.t()])
  end

  @type program :: [{key(), [Clause.t()]}]

  @typedoc "What unfolding leaves. `{:known, a, b}` is an equation the next pass may assume."
  @type item ::
          Call.t()
          | Primitive.t()
          | {:eq, Term.t(), Term.t()}
          | {:known, Term.t(), Term.t()}

  @type env :: %{name() => Term.t()}
  @type ctx :: %{scope: %{atom() => Rel.t()}, key: key(), root?: boolean()}

  @typedoc "What a rule makes of a call: items, the bindings after, and the goals in its place."
  @type rule :: (Rel.t(), [Term.t()], env(), [step()], ctx() ->
                   {[item()], env(), [Term.goal()]} | nil)

  @doc "I am the rules for a call, in the order they are tried."
  @spec call_rules() :: [{:needed | :cheaper, rule()}]
  def call_rules do
    [
      needed: &natural/5,
      cheaper: &Lookup.nth/5,
      cheaper: &Lookup.lookup/5,
      cheaper: &Array.array/5,
      cheaper: &Traversal.step/5,
      cheaper: &Traversal.start/5,
      cheaper: &Inline.only_clause/5,
      needed: &member_call/5
    ]
  end

  @doc "I am the members `root` needs, root first, each with its unfolded clauses."
  @spec program(Rel.t(), %{atom() => Rel.t()}) :: program()
  def program(root = %Rel{}, scope) do
    [{root.name, List.duplicate(nil, root.arity)}]
    |> members([], scope)
    |> Recursion.linear()
  end

  @spec members([key()], program(), %{atom() => Rel.t()}) :: program()
  defp members([], done, _scope), do: Enum.reverse(done)

  defp members([key = {name, handed} | queue], done, scope) do
    if List.keymember?(done, key, 0) do
      members(queue, done, scope)
    else
      clauses = scope[name].clauses
      # Only a root with a single clause lays its arrays along the columns.
      ctx = %{scope: scope, key: key, root?: done == [] and length(clauses) == 1}

      unfolded =
        for {head, body} <- clauses do
          {parameters, env} = passed(head, handed)
          env = Map.merge(env, Traversal.rows(head, handed))
          clause(parameters, qualify_locals(parameters, body), env, ctx)
        end

      called = for %Clause{calls: calls} <- unfolded, %Call{member: member} <- calls, do: member
      members(queue ++ called, [{key, unfolded} | done], scope)
    end
  end

  # Names that are not in the head get an empty path, so only head names are atoms.
  @spec qualify_locals([Term.t()], [Term.goal()]) :: [Term.goal()]
  defp qualify_locals(head, body) do
    heads = Term.names(head)
    Inline.rename(body, fn var = {:var, v} -> if v in heads, do: var, else: {:var, {[], v}} end)
  end

  # What a parameter is handed decides what is left of it in the head. A constant leaves
  # nothing. A passed relation leaves its fixed arguments. In both cases the name stands
  # for what was handed.
  @spec passed([Term.t()], [handed()]) :: {[Term.t()], env()}
  defp passed(head, handed) do
    parts =
      for pair <- Enum.zip(head, handed) do
        case pair do
          {{:var, v}, {:fixed, term}} ->
            {[], %{{[], v} => term}}

          {{:var, r}, {:relation, p, n}} ->
            fixed = for i <- 1..n//1, do: {:var, :"#{r}.#{i}"}
            {fixed, %{{[], r} => {:papply, p, fixed}}}

          {pattern, _other} ->
            {[pattern], %{}}
        end
      end

    {Enum.flat_map(parts, &elem(&1, 0)), Enum.reduce(parts, %{}, &Map.merge(elem(&1, 1), &2))}
  end

  # I unfold the body until a pass learns nothing new: numbers and array cells found in one
  # pass are known from the start of the next, so a goal can use what is declared after it.
  @spec clause([Term.t()], [Term.goal()], env(), ctx()) :: Clause.t()
  defp clause(head, body, env, ctx) do
    {items, learned} = goals(body, env, [], ctx)

    numbers =
      Map.filter(learned, fn {v, _term} -> is_integer(Bindings.resolve({:var, v}, learned)) end)

    known =
      for({:known, a, b} <- items, reduce: env, do: (env -> Bindings.unify(a, b, env) || env))
      |> Map.merge(numbers)

    if known != env, do: clause(head, body, known, ctx), else: Solve.clause(head, items, learned)
  end

  # The body's equations are unified first, so they apply whatever order they are in.
  @spec goals([Term.goal()], env(), [step()], ctx()) :: {[item()], env()}
  defp goals(goals, env, path, ctx) do
    env = for {:eq, a, b} <- goals, reduce: env, do: (env -> Bindings.unify(a, b, env) || env)

    {items, env, _called} =
      Enum.reduce(goals, {[], env, []}, fn goal, {items, env, called} ->
        {more, env, called} = goal(goal, env, called, path, ctx)
        {items ++ more, env, called}
      end)

    {items, env}
  end

  # `called` is the relations the body has called so far: a call's step is its relation and
  # its position among the calls to it.
  @spec goal(Term.goal(), env(), [atom()], [step()], ctx()) :: {[item()], env(), [atom()]}
  defp goal({:eq, a, b}, env, called, _path, _ctx) do
    # An equation that cannot hold becomes `0 = 1`, which makes the clause dead.
    case Bindings.unify(a, b, env) do
      nil -> {[{:eq, 0, 1}], env, called}
      env -> {[{:eq, a, b}], env, called}
    end
  end

  defp goal({:call, q, args}, env, called, path, ctx) do
    {rel, args} = Bindings.callee(q, args, env, ctx.scope)
    path = path ++ [{rel.name, Enum.count(called, &(&1 == rel.name))}]
    apply = fn {_kind, rule} -> rule.(rel, args, env, path, ctx) end
    {items, unfolded, replaced_by} = Enum.find_value(call_rules(), apply)
    {more, unfolded} = goals(replaced_by, unfolded, path, ctx)
    name = rel.name

    # When what replaced the call still calls the relation, the call is made instead:
    # the caller would pay for the unfolded steps and for the member.
    if Enum.any?(more, &match?(%Call{member: {^name, _handed}, at: :pointer}, &1)) do
      {call, env, []} = member_call(rel, args, env, path, ctx)
      {call, env, [name | called]}
    else
      {items ++ more, unfolded, [name | called]}
    end
  end

  @spec natural(Rel.t(), [Term.t()], env(), [step()], ctx()) ::
          {[item()], env(), [Term.goal()]} | nil
  defp natural(%Rel{phi: {Ast, :natural}}, [x], env, _path, _ctx),
    do: {[%Primitive{op: :natural, args: [x]}], env, []}

  defp natural(_rel, _args, _env, _path, _ctx), do: nil

  # A pointer call to the member for the relation and the relations it is passed. A
  # passed relation's fixed arguments are passed in its place.
  @spec member_call(Rel.t(), [Term.t()], env(), [step()], ctx()) ::
          {[item()], env(), [Term.goal()]}
  defp member_call(rel, args, env, path, _ctx) do
    {handed, args} =
      Enum.unzip(
        for arg <- args do
          case Bindings.resolve(arg, env) do
            {:papply, p, fixed} -> {{:relation, p, length(fixed)}, fixed}
            _value -> {nil, [arg]}
          end
        end
      )

    call = %Call{source: path, member: {rel.name, handed}, args: Enum.concat(args), at: :pointer}
    {[call], env, []}
  end
end
