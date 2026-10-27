defmodule Zkfol.Derivation do
  @moduledoc """
  I am the extension a run established: the facts in callees-first order,
  the consumption between them, and the clause each fact fired. A fact is
  its own key: nothing outside me counts my positions. `bindings` retains the chosen
  clause's source variables beside its fact, including locals absent from its arguments.
  """

  use TypedStruct

  alias Zkfol.Al
  alias Zkfol.Lang.{Rel, Term}

  @typedoc "One established fact: the relation and its ground tuple."
  @type fact :: {atom(), [term()]}

  typedstruct enforce: true do
    field(:facts, [fact()])
    # Pairs, not maps: a tuple key cannot ride the bridge.
    field(:consumed, [{fact(), [fact()]}], default: [])
    field(:clauses, [{fact(), non_neg_integer() | nil}], default: [])
    field(:bindings, [{fact(), %{atom() => term()}}], default: [])
  end

  @doc """
  I am the derivation AL's journal carries, deduplicated, callees ahead of their callers;
  each fact sits beside what its calls consumed and the seq that established it.
  """
  @typedoc "The source relations by their installed AL method names."
  @type methods :: %{atom() => Rel.t()}

  @spec of(AL.JAM.State.t(), [Rel.t()]) :: t()
  def of(state = %AL.JAM.State{active_choicepoint: %{store: store}}, rels) do
    names = Map.new(rels, &{Al.method(&1.name), &1})

    nodes =
      state
      |> AL.Trace.derivation_tree()
      |> calls()
      |> Enum.flat_map(&walk(&1, names, store))

    facts = nodes |> Enum.map(&elem(&1, 0)) |> Enum.uniq()
    digested = Map.new(nodes)
    ran = for fact <- facts, do: {fact, Map.fetch!(digested, fact)}

    %__MODULE__{
      facts: facts,
      consumed: for({fact, {callees, _clause, _bindings}} <- ran, do: {fact, callees}),
      clauses: for({fact, {_callees, clause, _bindings}} <- ran, do: {fact, clause}),
      bindings: for({fact, {_callees, _clause, bindings}} <- ran, do: {fact, bindings})
    }
  end

  @doc "I am the facts one fact's calls consumed, in body order."
  @spec consumed(t(), fact()) :: [fact()]
  def consumed(%__MODULE__{consumed: consumed}, fact),
    do: consumed |> List.keyfind(fact, 0, {fact, []}) |> elem(1)

  @doc "I am the 0-based seq of the clause that established one fact."
  @spec clause(t(), fact()) :: non_neg_integer() | nil
  def clause(%__MODULE__{clauses: clauses}, fact),
    do: clauses |> List.keyfind(fact, 0, {fact, nil}) |> elem(1)

  @doc "I am what a run established of one relation: its last fact, the query's own."
  @spec root(t(), atom()) :: fact() | nil
  def root(%__MODULE__{facts: facts}, relation),
    do: facts |> Enum.reverse() |> Enum.find(&(elem(&1, 0) == relation))

  @doc "I am each fact beside what it consumed, in my order."
  @spec consumption(t()) :: [{fact(), [fact()]}]
  def consumption(%__MODULE__{consumed: consumed}), do: consumed

  # A call is a method node beside the answer it gave: the clause chosen, what it derived and
  # the nodes beneath. Every other node only holds calls.
  @spec calls([map()]) :: [{term(), map()}]
  defp calls(nodes) do
    Enum.flat_map(nodes, fn
      %{kind: :method, label: label, children: answers} -> for a <- answers, do: {label, a}
      %{children: kids} -> calls(kids)
    end)
  end

  @spec walk({term(), map()}, methods(), map()) :: [
          {fact(), {[fact()], non_neg_integer() | nil, %{atom() => term()}}}
        ]
  defp walk({label, answer}, names, store) do
    kids = calls(answer.children)
    below = Enum.flat_map(kids, &walk(&1, names, store))

    if fact?(label, names) do
      consumed =
        for {kid, kid_answer} <- kids,
            fact?(kid, names),
            do: fact_of(kid, kid_answer.derived, names, store)

      {_self, method, _args} = label
      {head, body} = names[method].clauses |> Enum.at(answer.clause)

      bindings =
        Map.new(Term.names(head ++ body), fn name ->
          {name, answer.bindings |> Map.fetch!(Al.var(name)) |> AL.Var.subst(store)}
        end)

      below ++
        [{fact_of(label, answer.derived, names, store), {consumed, answer.clause, bindings}}]
    else
      below
    end
  end

  # I match a journal node to a relation by its method name and arity.
  @spec fact?(term(), methods()) :: boolean()
  defp fact?({_self, m, args}, names) do
    case Map.get(names, m) do
      %Rel{arity: arity} -> arity == length(args)
      nil -> false
    end
  end

  defp fact?(_label, _names), do: false

  @spec fact_of(term(), map() | nil, methods(), map()) :: fact()
  defp fact_of({_self, m, args}, derived, names, store) do
    %Rel{name: name} = Map.fetch!(names, m)

    values =
      for arg <- args, do: arg |> resolved(derived) |> AL.Var.subst(store)

    {name, values}
  end

  # A sequence built one call at a time was journalled with its tail still open.
  @spec resolved(term(), map() | nil) :: term()
  defp resolved([head | tail], derived), do: [resolved(head, derived) | resolved(tail, derived)]

  defp resolved(term, derived) do
    case derived && Map.get(derived, term) do
      {:bound, value} -> resolved(value, derived)
      _open -> term
    end
  end

  @doc "I am the derivation beneath one fact: it and everything it consumed, transitively."
  @spec under(t(), fact()) :: t()
  def under(t = %__MODULE__{}, fact) do
    kept = reach([fact], t, MapSet.new())

    %__MODULE__{
      facts: Enum.filter(t.facts, &MapSet.member?(kept, &1)),
      consumed: Enum.filter(t.consumed, &MapSet.member?(kept, elem(&1, 0))),
      clauses: Enum.filter(t.clauses, &MapSet.member?(kept, elem(&1, 0))),
      bindings: Enum.filter(t.bindings, &MapSet.member?(kept, elem(&1, 0)))
    }
  end

  @spec reach([fact()], t(), MapSet.t()) :: MapSet.t()
  defp reach([], _t, seen), do: seen

  defp reach([fact | rest], t, seen) do
    if MapSet.member?(seen, fact),
      do: reach(rest, t, seen),
      else: reach(consumed(t, fact) ++ rest, t, MapSet.put(seen, fact))
  end

  @doc "I replace every variable left free by unification with zero, at any depth of the value."
  @spec free_to_zero(term()) :: term()
  def free_to_zero(list) when is_list(list), do: Enum.map(list, &free_to_zero/1)
  def free_to_zero({:node, term}), do: {:node, free_to_zero(term)}
  def free_to_zero(cell), do: if(AL.Var.var?(cell), do: 0, else: cell)
end

defimpl Inspect, for: Zkfol.Derivation do
  import Inspect.Algebra

  # `fib(3, 2)<-{0,1}`: this fact consumed facts 0 and 1, in body order.
  def inspect(derivation = %Zkfol.Derivation{facts: facts}, _opts) do
    at = facts |> Enum.with_index() |> Map.new()

    lines =
      for {{name, tuple}, used} <- Zkfol.Derivation.consumption(derivation) do
        stated = "#{name}(#{cells(tuple)})"
        if used == [], do: stated, else: stated <> "<-{#{Enum.map_join(used, ",", &at[&1])}}"
      end

    concat(["#Zkfol.Derivation<", Enum.join(lines, " "), ">"])
  end

  defp cells(tuple), do: Enum.map_join(tuple, ", ", &inspect/1)
end
