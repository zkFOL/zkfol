defmodule Zkfol.Phi.Storage do
  @moduledoc """
  I decide how each member's parameters are stored, before any clause is compiled.

  A parameter used as a number is a cell and one used as a list is a heap term. An array
  the root declares is stored along the columns. A parameter no goal uses has no storage.
  A walking member reads the root's arrays at its own column.

  ### Public API

  - `of/3`: every member's interface.
  """

  use TypedStruct

  alias Zkfol.Alloc.{Bank, Slot, Source}
  alias Zkfol.Ast
  alias Zkfol.Lang.{Rel, Term}
  alias Zkfol.Phi.{Match, Place}
  alias Zkfol.Unfold
  alias Zkfol.Unfold.{Call, Clause, Primitive}

  typedstruct module: Interface, enforce: true do
    @moduledoc "I am a member's name, the value of each parameter, and the rows it needs."
    field(:name, atom())
    field(:relation, atom())
    field(:values, [Zkfol.Phi.Match.value() | nil])
    field(:slots, [Zkfol.Alloc.Slot.t()])
    field(:banks, [Zkfol.Alloc.Bank.t()])
    field(:steps, {non_neg_integer(), integer()} | nil)
  end

  @typedoc """
  How a name is used. `:used` and `:element` only say that it needs storage: `:used` is
  stored as a number and `:element`, an element of a list, as a heap term, unless another
  use says more.
  """
  @type kind :: :number | :term | :used | :element | {:bank, [non_neg_integer()]}

  # A parameter of a member, or a name in one of its clauses.
  @typep holder ::
           {Unfold.key(), non_neg_integer()} | {Unfold.key(), non_neg_integer(), Unfold.name()}
  @typep fact :: {holder(), kind() | nil | {:same, holder()}}

  @doc "I am every member's interface; `args` are the values the root was given."
  @spec of(Unfold.program(), %{atom() => Rel.t()}, [term()]) :: %{Unfold.key() => Interface.t()}
  def of(program = [{root = {relation, _handed}, _clauses} | _], scope, args) do
    kinds = kinds(program, root, args)

    {interfaces, _taken} =
      Enum.map_reduce(program, [], fn {key = {name, _handed}, _clauses}, taken ->
        candidates = [name | for(i <- 2..(length(taken) + 2), do: :"#{name}#{i}")]
        member = Enum.find(candidates, &(&1 not in taken))
        {{key, interface(key, member, scope[name], kinds, relation)}, [member | taken]}
      end)

    Map.new(interfaces)
  end

  @spec interface(Unfold.key(), atom(), Rel.t(), %{holder() => kind()}, atom()) :: Interface.t()
  defp interface(key = {relation, handed}, name, rel, kinds, root) do
    # A constant is no parameter, and a passed relation's fixed arguments are parameters
    # in its place.
    sources =
      for {{sym, handed}, k} <- Enum.with_index(Enum.zip(parameter_names(rel), handed)),
          source <-
            (case handed do
               {:fixed, _term} ->
                 []

               {:relation, _p, n} ->
                 for(i <- 1..n//1, do: {:"#{sym}.#{i}", nil, {:fixed, k, i - 1}})

               other ->
                 [{sym, other, {:argument, k}}]
             end),
          do: source

    parameters =
      for {{sym, handed, binding}, k} <- Enum.with_index(sources) do
        slot = %Slot{name: sym, allocation: :none, source: %Source{binding: binding}}
        parameter(handed, kinds[{key, k}], {name, {:param, sym}}, slot, root)
      end

    %Interface{
      name: name,
      relation: relation,
      values: Enum.map(parameters, &elem(&1, 0)),
      slots: Enum.map(parameters, &elem(&1, 1)),
      banks: Enum.flat_map(parameters, &elem(&1, 2)),
      steps:
        Enum.find_value(
          Enum.with_index(handed),
          &(match?({{:bank, _, _}, _k}, &1) && {elem(&1, 1), -1})
        )
    }
  end

  # A parameter's value, its slot and the bank it declares.
  @spec parameter(Unfold.handed(), kind() | nil, Ast.row_ref(), Slot.t(), atom()) ::
          {Match.value() | nil, Slot.t(), [Bank.t()]}
  defp parameter({:bank, array, inner}, _kind, _ref, slot, root) do
    bank = Bank.of({root, {:param, array}})
    {%Place.View{bank: bank, head: Ast.address(:x, 1, 0), dimensions: inner}, slot, []}
  end

  defp parameter(nil, kind, ref, slot, _root) when kind in [:number, :used],
    do: {Ast.cell(ref), %{slot | allocation: {:cell, ref}}, []}

  defp parameter(nil, kind, ref, slot, _root) when kind in [:term, :element],
    do: {{:node, Ast.cell(ref)}, %{slot | allocation: {:node, ref}}, []}

  defp parameter(nil, {:bank, [n | inner]}, ref, slot, _root) do
    bank = %Bank{name: Bank.of(ref), depth: max(1, Enum.product(inner))}
    view = %Place.View{bank: bank.name, head: Ast.address(:x, 0, n + 1), dimensions: inner}
    {view, %{slot | allocation: {:bank, bank.name, n}}, [bank]}
  end

  defp parameter(nil, _unused, _ref, slot, _root), do: {nil, slot, []}

  @spec parameter_names(Rel.t()) :: [atom()]
  defp parameter_names(%Rel{clauses: clauses}) do
    {head, _body} = Enum.max_by(clauses, fn {_head, body} -> length(body) end)

    for {pattern, k} <- Enum.with_index(head) do
      case pattern do
        {:var, name} -> name
        _pattern -> :"a#{k + 1}"
      end
    end
  end

  ############################################################
  #                          Kinds                           #
  ############################################################

  # I collect how every clause uses its names, then pass kinds between names that must
  # agree until nothing changes.
  @spec kinds(Unfold.program(), Unfold.key(), [term()]) :: %{holder() => kind()}
  defp kinds(program, root, args) do
    given = for {arg, k} <- Enum.with_index(args), do: {{root, k}, argument_kind(arg)}

    facts =
      for {key, clauses} <- program, {clause, c} <- Enum.with_index(clauses) do
        name = &{key, c, &1}
        goals = clause.calls ++ clause.equations ++ clause.primitives
        [head_facts(clause, key, name) | Enum.map(goals, &facts(&1, name))]
      end

    facts = List.flatten([given | facts])
    kinds = propagate(%{}, for({holder, kind} <- facts, kind != nil, do: {holder, kind}))

    # A declared array of the root is stored along the columns whatever its other uses.
    for {{:bank, dims}, holder} <- facts, into: kinds, do: {holder, {:bank, dims}}
  end

  @spec argument_kind(term()) :: kind() | nil
  defp argument_kind(arg) when is_list(arg), do: :term
  defp argument_kind(arg) when is_integer(arg), do: :number
  defp argument_kind(_unknown), do: nil

  # A head name has its parameter's kind. A head name the clause uses, or writes twice
  # in the head, needs storage even when nothing says what it is: an equation between
  # two such names still has to be constrained.
  @spec head_facts(Clause.t(), Unfold.key(), (Unfold.name() -> holder())) :: [fact()]
  defp head_facts(clause = %Clause{head: head, banks: banks}, key, name) do
    used =
      Enum.flat_map(clause.equations, &Term.names(Tuple.to_list(&1))) ++
        Enum.flat_map(clause.calls ++ clause.primitives, &Term.names(&1.args)) ++
        (Term.names(head) -- Enum.uniq(Term.names(head)))

    for {pattern, k} <- Enum.with_index(head) do
      case pattern do
        {:var, v} ->
          bank = for {^v, dims} <- banks, do: {{:bank, dims}, {key, k}}
          [{{key, k}, {:same, name.(v)}}, {{key, k}, if(v in used, do: :used)} | bank]

        other ->
          [{{key, k}, shape(other)} | inner(other, name)]
      end
    end
  end

  @spec facts(Call.t() | {Term.t(), Term.t()} | Primitive.t(), (Unfold.name() -> holder())) ::
          [fact()]
  defp facts({{:var, a}, {:var, b}}, name), do: [{name.(a), {:same, name.(b)}}]

  defp facts({a, b}, name) do
    for({{:var, v}, other} <- [{a, b}, {b, a}], do: {name.(v), shape(other)}) ++
      inner(a, name) ++ inner(b, name)
  end

  defp facts(%Call{member: member, args: args}, name) do
    for {arg, k} <- Enum.with_index(args) do
      case arg do
        {:var, v} -> [{name.(v), {:same, {member, k}}}]
        other -> [{{member, k}, shape(other)} | inner(other, name)]
      end
    end
  end

  defp facts(%Primitive{args: args}, name),
    do: for(v <- Term.names(args), do: {name.(v), :number})

  @spec shape(term()) :: kind() | nil
  defp shape(q) when is_integer(q), do: :number
  defp shape(:len), do: :number
  defp shape({op, _, _}) when op in [:add, :mul], do: :number
  defp shape({:cons, _, _}), do: :term
  defp shape(nil), do: :term

  # The facts about the names inside a term.
  @spec inner(term(), (Unfold.name() -> holder())) :: [fact()]
  defp inner({op, a, b}, name) when op in [:add, :mul],
    do: for({:var, v} <- [a, b], do: {name.(v), :number}) ++ inner(a, name) ++ inner(b, name)

  defp inner({:cons, h, t}, name),
    do: for({:var, v} <- [h, t], do: {name.(v), :element}) ++ inner(h, name) ++ inner(t, name)

  defp inner(_leaf, _name), do: []

  @spec propagate(%{holder() => kind()}, [fact()]) :: %{holder() => kind()}
  defp propagate(kinds, facts) do
    more =
      Enum.reduce(facts, kinds, fn
        {{:bank, _dims}, _holder}, kinds -> kinds
        {a, {:same, b}}, kinds -> kinds |> merge(a, kinds[b]) |> merge(b, kinds[a])
        {holder, kind}, kinds -> merge(kinds, holder, kind)
      end)

    if more == kinds, do: kinds, else: propagate(more, facts)
  end

  # A name used both as a number and as a list is a heap term. `:used` and `:element`
  # give way to any other kind.
  @spec merge(%{holder() => kind()}, holder(), kind() | nil) :: %{holder() => kind()}
  defp merge(kinds, _holder, nil), do: kinds

  defp merge(kinds, holder, kind) do
    Map.update(kinds, holder, kind, fn
      ^kind -> kind
      held when held in [:used, :element] and kind in [:used, :element] -> :element
      held when held in [:used, :element] -> kind
      held -> if kind in [:used, :element], do: held, else: :term
    end)
  end
end
