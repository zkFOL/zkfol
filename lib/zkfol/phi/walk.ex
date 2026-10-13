defmodule Zkfol.Phi.Walk do
  @moduledoc """
  I retain the bindings, equations and allocation decisions made while compiling a clause.

  `env` retains source definitions, including aliases and unfinished constructors.
  Inlined names remain available until the member is compiled. Parameter references
  bind physical accesses; retaining a source definition does not allocate storage.
  `parameters` records each parameter's allocation; `:none` means it shares an
  existing access. Array views carry their complete dimensions.
  `slots` holds local storage.
  An impossible walk is `:dead`.
  A member retains its clauses; each clause's body retains the clauses of members it calls.

  ### Public API

  - `fetch/2`, `follow/2`: follow aliases and read values.
  - `merge/2`: combine parameter declarations.
  - `constrain/2`: retain the equations required by an observation.
  - `bind/3`: record a parameter's access and explicit allocation.
  - `banks/1`: the banks owned by parameter allocations.
  - `peel/2`, `ended/2`: observe a source bracket, recording its storage requirements.
  """

  use TypedStruct
  use GtBridge.View

  alias GtBridge.Phlow.ColumnedList
  alias Zkfol.Alloc.Bank
  alias Zkfol.Alloc.Member
  alias Zkfol.Alloc.Site
  alias Zkfol.Alloc.Slot
  alias Zkfol.Ast
  alias Zkfol.Phi.{Expression, Place, Value}
  alias Zkfol.Phi.Place.Binding

  require Place

  defmodule Clause do
    @moduledoc "I retain one compiled clause's inputs and the walks before and after its rules."
    use TypedStruct
    use GtBridge.View
    alias GtBridge.Phlow.ColumnedList

    typedstruct enforce: true do
      field(:member, atom())
      field(:head, [term()])
      field(:body, [term()])
      field(:accesses, [Zkfol.Phi.Value.t()])
      field(:before, Zkfol.Phi.Walk.t())
      field(:matched, Zkfol.Phi.Walk.t() | :dead)
      field(:compiled, Zkfol.Phi.Walk.t() | :dead)
    end

    defview inputs_view(%Zkfol.Phi.Walk.Clause{head: head, accesses: accesses}, builder) do
      builder.columned_list()
      |> ColumnedList.title("Inputs")
      |> ColumnedList.priority(1)
      |> ColumnedList.items(Enum.zip(head, accesses))
      |> ColumnedList.column("Pattern", fn {pattern, _access} ->
        Zkfol.Face.surface_text(pattern)
      end)
      |> ColumnedList.column("Access", fn {_pattern, access} -> Zkfol.Face.inspected(access) end)
      |> ColumnedList.send(fn {_pattern, access} -> access end)
    end

    defview steps_view(clause = %Zkfol.Phi.Walk.Clause{}, builder) do
      builder.columned_list()
      |> ColumnedList.title("Steps")
      |> ColumnedList.priority(2)
      |> ColumnedList.items([
        {"Before head", clause.before},
        {"After head", clause.matched},
        {"After body", clause.compiled}
      ])
      |> ColumnedList.column("Step", fn {name, _state} -> name end)
      |> ColumnedList.send(fn {_name, state} -> state end)
    end
  end

  typedstruct do
    field(:env, %{(Expression.name() | Ast.row_ref()) => Expression.symbolic()}, default: %{})
    field(:parameters, %{Ast.row_ref() => Zkfol.Alloc.allocation()}, default: %{})
    field(:members, [Member.t() | Bank.t()], default: [])
    field(:predicates, [Ast.pred()], default: [])
    field(:eqs, [Ast.pred()], default: [])
    field(:sites, [{non_neg_integer(), Site.t()}], default: [])
    field(:slots, [Slot.t()], default: [])
    field(:clauses, [Clause.t()], default: [])
  end

  @doc "I merge a parameter declaration into a walk; the declaration's entries take precedence."
  @spec merge(t(), t()) :: t()
  def merge(declaration = %__MODULE__{}, walk = %__MODULE__{}) do
    %{
      walk
      | env: Map.merge(walk.env, declaration.env),
        parameters: Map.merge(walk.parameters, declaration.parameters)
    }
  end

  @doc "I collect conjuncts in reverse order without copying the clause accumulated so far."
  @spec constrain(t(), [Ast.pred(Value.scalar())]) :: t()
  def constrain(walk = %__MODULE__{}, eqs) do
    # A record read as a number has no number: its fields came back as a list.
    for eq <- eqs, Ast.reduce(eq, false, &(&2 or is_list(&1))) do
      throw({:refused, {:unliftable_term, %{term: eq}}})
    end

    %{walk | eqs: Enum.reverse(eqs, walk.eqs)}
  end

  @doc "I follow a name's definitions, retaining unknown variables."
  @spec fetch(t(), term()) :: Expression.symbolic()
  def fetch(walk, name), do: Expression.substitute(Map.fetch!(walk.env, name), walk)

  @doc "I follow parameter aliases, retaining an unresolved reference's identity."
  @spec follow(t(), Value.t()) :: Value.t()
  def follow(walk, fresh = {:fresh, ref}) do
    case Map.fetch(walk.env, ref) do
      {:ok, value} -> follow(walk, value)
      :error -> fresh
    end
  end

  def follow(_walk, value), do: value

  @doc "I record an explicit binding; an unresolved parameter has no binding yet."
  @spec bind(t(), Ast.row_ref(), Binding.t() | nil) :: t()
  def bind(walk, _ref, nil), do: walk

  def bind(walk, ref, %Binding{value: value, allocation: allocation}),
    do: %{
      walk
      | env: Map.put(walk.env, ref, value),
        parameters: Map.put(walk.parameters, ref, allocation)
    }

  @doc "I return the banks owned by parameter allocations."
  @spec banks(t()) :: [atom()]
  def banks(%__MODULE__{parameters: parameters}) do
    for {_ref, {:bank, name, _extent}} <- parameters, do: name
  end

  @doc "I peel a declared view, pair or heap term."
  @spec peel(t(), Expression.symbolic()) ::
          {:ok, Expression.symbolic(), Expression.symbolic(), t()} | :dead
  def peel(walk, {tag, head, tail}) when tag in [:pair, :cons], do: {:ok, head, tail, walk}
  def peel(walk, [head | tail]), do: {:ok, head, tail, walk}

  def peel(walk, view) when Place.is_laid(view) do
    with walk = %__MODULE__{} <- presence(walk, view, 1),
         do: {:ok, Place.slice(view, 0), Place.shifted(view, 1), walk}
  end

  def peel(walk, {:node, id}) do
    {:ok, {:node, Place.read(:head, id)}, {:node, Place.read(:tail, id)},
     constrain(walk, [Ast.eq(Place.read(:tag, id), 2)])}
  end

  def peel(_walk, _value), do: :dead

  @doc "I require a view or heap sequence to end."
  @spec ended(t(), Value.t()) :: t() | :dead
  def ended(walk, []), do: walk
  def ended(walk, view) when Place.is_laid(view), do: presence(walk, view, 0)
  def ended(walk, {:node, id}), do: constrain(walk, [Ast.eq(id, 1)])
  def ended(_walk, _value), do: :dead

  # A known length decides presence; otherwise the bank's presence cell must say it.
  defp presence(walk, along, required) do
    case Place.count(along) do
      nil -> constrain(walk, [Ast.eq(Place.presence(along), required)])
      0 when required == 0 -> walk
      n when n > 0 and required == 1 -> walk
      _other -> :dead
    end
  end

  ############################################################
  #                            Views                         #
  ############################################################

  defview predicates_view(%Zkfol.Phi.Walk{predicates: predicates}, builder) do
    builder.columned_list()
    |> ColumnedList.title("Predicates")
    |> ColumnedList.priority(5)
    |> ColumnedList.items(predicates)
    |> ColumnedList.column("Predicate", &Zkfol.Face.phi_text/1)
  end

  defview bindings_view(walk = %Zkfol.Phi.Walk{env: env}, builder) do
    builder.columned_list()
    |> ColumnedList.title("Bindings")
    |> ColumnedList.priority(2)
    |> ColumnedList.items(
      for {name, _access} <- Enum.sort(env), do: {name, Zkfol.Phi.Walk.fetch(walk, name)}
    )
    |> ColumnedList.column("Name", fn {name, _access} -> inspect(name) end)
    |> ColumnedList.column("Access", fn {_name, access} -> Zkfol.Face.inspected(access) end)
    |> ColumnedList.send(fn {_name, access} -> access end)
  end

  defview equations_view(%Zkfol.Phi.Walk{eqs: eqs}, builder) do
    builder.columned_list()
    |> ColumnedList.title("Equations")
    |> ColumnedList.priority(3)
    |> ColumnedList.items(Enum.reverse(eqs))
    |> ColumnedList.column("Equation", &Zkfol.Face.phi_text/1)
  end

  defview storage_view(walk = %Zkfol.Phi.Walk{}, builder) do
    builder.columned_list()
    |> ColumnedList.title("Storage")
    |> ColumnedList.priority(4)
    |> ColumnedList.items([
      {"Owned banks", Zkfol.Phi.Walk.banks(walk)},
      {"Parameters", walk.parameters},
      {"Slots", walk.slots},
      {"Members", walk.members}
    ])
    |> ColumnedList.column("What", fn {name, _value} -> name end)
    |> ColumnedList.column("Value", fn {_name, value} -> Zkfol.Face.inspected(value) end)
    |> ColumnedList.send(fn {_name, value} -> value end)
  end
end
