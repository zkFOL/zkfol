defmodule Zkfol.Phi.Walk do
  @moduledoc """
  I retain the bindings, equations and allocation decisions made while compiling a clause.

  `env` retains source definitions, including aliases and unfinished constructors.
  Inlined names remain available until the member is compiled. Parameter references
  bind physical accesses; retaining a source definition does not allocate storage.
  `parameters` records each parameter's allocation; `:none` means it shares an
  existing access. `shapes` records observations of owned or borrowed elements.
  `slots` holds local storage.
  `mode` distinguishes a member, an inline trial and a wrapper expansion. A trial
  records required banks and callees; a wrapper may realize its callees. Both retain
  scalar slots supplied by source bindings. Rejecting an expansion discards its slots.
  Either may resolve an enclosing member's parameter storage and continue looking for
  contradictions.
  An impossible walk is `:dead`.
  A member retains its clauses; each clause's body retains the clauses of members it calls.

  ### Public API

  - `fetch/2`, `follow/2`: follow aliases and read values with their resolved element shapes.
  - `refine/2`: retain element shape requirements.
  - `merge/2`: combine parameter declarations.
  - `constrain/2`: retain the equations required by an observation.
  - `bind/3`, `bind/4`: bind a parameter and record its allocation.
  - `allocate/3`: choose storage for a newly resolved parameter.
  - `banks/1`: the banks owned by parameter allocations.
  - `require/2`: record storage an inline clause would need.
  - `bank/3`, `bank/4`: give an unresolved parameter its own sequence storage.
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
  alias Zkfol.Phi.{Expression, Place, Shape, Value}

  require Place

  @typedoc "Storage an inline clause would need beyond the enclosing member's parameters."
  @type requirement :: {:member, atom()} | {:bank, Ast.row_ref()}
  @type mode :: :member | {:inline | :wrapper, [requirement()]}

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
    field(:mode, mode(), default: :member)
    field(:env, %{(Expression.name() | Ast.row_ref()) => Expression.symbolic()}, default: %{})
    field(:shapes, %{Ast.row_ref() => Shape.t()}, default: %{})
    field(:parameters, %{Ast.row_ref() => Zkfol.Alloc.allocation()}, default: %{})
    field(:members, [Member.t() | Bank.t()], default: [])
    field(:predicates, [Ast.pred()], default: [])
    field(:eqs, [Ast.pred()], default: [])
    field(:sites, [{non_neg_integer(), Site.t()}], default: [])
    field(:slots, [Slot.t()], default: [])
    field(:clauses, [Clause.t()], default: [])
  end

  @doc "I record an inline clause's storage requirement and continue interpreting its goals."
  @spec require(t(), requirement()) :: t()
  def require(walk = %__MODULE__{mode: {kind, required}}, requirement),
    do: %{walk | mode: {kind, [requirement | required]}}

  @doc "I merge a parameter declaration into a walk; the declaration's entries take precedence."
  @spec merge(t(), t()) :: t()
  def merge(declaration = %__MODULE__{}, walk = %__MODULE__{}) do
    %{
      walk
      | env: Map.merge(walk.env, declaration.env),
        parameters: Map.merge(walk.parameters, declaration.parameters),
        shapes: merge_shapes(walk.shapes, declaration.shapes)
    }
  end

  @doc "I collect conjuncts in reverse order without copying the clause accumulated so far."
  @spec constrain(t(), [Ast.pred(Value.scalar())]) :: t()
  def constrain(walk = %__MODULE__{}, eqs) do
    required =
      eqs
      |> Enum.flat_map(
        &Ast.reduce(&1, [], fn
          {:across, row, _address, 0}, rows -> [row | rows]
          _term, rows -> rows
        end)
      )
      |> Enum.reject(&match?({:list, _, _}, Map.get(walk.shapes, &1)))
      |> Map.new(&{&1, :scalar})

    walk = refine(walk, required)
    eqs = Enum.map(eqs, &Value.shaped(&1, walk.shapes))

    # A record read as a number has no number: its fields came back as a list.
    for eq <- eqs, Ast.reduce(eq, false, &(&2 or is_list(&1))) do
      throw({:refused, {:unliftable_term, %{term: eq}}})
    end

    %{walk | eqs: Enum.reverse(eqs, walk.eqs)}
  end

  @doc "I follow a name's definitions, retaining unknown variables and resolving known element shapes."
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

  def follow(walk, value), do: Value.shaped(value, walk.shapes)

  @doc "I retain compatible shape requirements, independently of storage ownership."
  @spec refine(t(), %{Ast.row_ref() => Shape.t()}) :: t()
  def refine(walk, shapes), do: %{walk | shapes: merge_shapes(walk.shapes, shapes)}

  defp merge_shapes(a, b) do
    Map.merge(a, b, fn row, x, y ->
      case Shape.meet(x, y) do
        :contradiction -> throw({:refused, {:unliftable_term, %{term: {row, x, y}}}})
        shape -> shape
      end
    end)
  end

  @doc """
  I bind a parameter to an access. A node in the parameter's cell owns it, as a passed
  relation owns the cells of its fixed arguments; a handed count gets a cell; the column
  uses no row; other accesses are shared. A fresh parameter waits for matching to resolve it.
  """
  @spec bind(t(), Ast.row_ref(), Value.t()) :: t()
  def bind(walk, _ref, :fresh), do: walk
  def bind(walk, _ref, {:fresh, _unplaced}), do: walk
  def bind(walk, ref, node = {:node, {:cell, ref}}), do: bind(walk, ref, node, {:node, ref})

  def bind(walk, ref, passed = {:rel, p, cells}),
    do: bind(walk, ref, passed, {:rel, p, Enum.map(cells, fn {:cell, row} -> row end)})

  def bind(walk, ref, {:count, q, _cell}),
    do: bind(walk, ref, {:count, q, Ast.cell(ref)}, {:cell, ref})

  def bind(walk, ref, :x), do: bind(walk, ref, :x, {:column, 0})
  def bind(walk, ref, access = {:add, :x, o}), do: bind(walk, ref, access, {:column, o})
  def bind(walk, ref, access), do: bind(walk, ref, access, :none)

  @doc "I bind a parameter and record the allocation required by that binding."
  @spec bind(t(), Ast.row_ref(), Value.t(), Zkfol.Alloc.allocation()) :: t()
  def bind(walk, ref, value, allocation),
    do: %{
      walk
      | env: Map.put(walk.env, ref, value),
        parameters: Map.put(walk.parameters, ref, allocation)
    }

  @doc """
  I choose storage for a newly resolved parameter. A list gets a node reference in its
  parameter cell, independent of the view selected by a clause. Already supplied accesses
  use `bind/3`. Matching then constrains the chosen access to equal the value.
  """
  @spec allocate(t(), Ast.row_ref(), Value.t()) :: t()
  def allocate(walk, ref, value) do
    cell = Ast.cell(ref)

    cond do
      is_integer(value) ->
        bind(walk, ref, {:count, value, cell}, {:cell, ref})

      is_list(value) or Place.is_laid(value) or match?({:pair, _, _}, value) or
          match?({:node, _id}, value) ->
        bind(walk, ref, {:node, cell}, {:node, ref})

      match?({:across, _, _, _}, value) or match?({:rel, _, _}, value) ->
        bind(walk, ref, value, :none)

      true ->
        bind(walk, ref, cell, {:cell, ref})
    end
  end

  @doc "I return the banks owned by parameter allocations."
  @spec banks(t()) :: [atom()]
  def banks(%__MODULE__{parameters: parameters}) do
    for {_ref, {:bank, name, _address}} <- parameters, do: name
  end

  @doc "I bind a parameter to the bank it is laid in and record the element shape of the bank's rows."
  @spec bank(t(), Ast.row_ref(), Place.t(), Shape.t()) :: t()
  def bank(walk = %__MODULE__{}, ref, laid = {:along, row = {bank, 1}, head}, shape) do
    {:list, _extent, element} = shape
    walk = bind(walk, ref, laid, {:bank, bank, head})
    if element == :unknown, do: walk, else: refine(walk, %{row => element})
  end

  @doc "I peel an unresolved record or an existing pair; ownership does not change its meaning."
  @spec peel(t(), Expression.symbolic()) ::
          {:ok, Expression.symbolic(), Expression.symbolic(), t()} | :dead
  def peel(walk, {:across, row = {bank, first}, col = {:at, base, m, a}, n}) do
    walk = refine(walk, %{row => {:list, {:at_least, n + 1}, :scalar}})
    {:ok, Ast.at({bank, first + n}, base, m, a), {:across, row, col, n + 1}, walk}
  end

  def peel(walk, value) do
    case Value.shaped(value, walk.shapes) do
      {tag, head, tail} when tag in [:pair, :cons] ->
        {:ok, head, tail, walk}

      [head | tail] ->
        {:ok, head, tail, walk}

      laid when Place.is_laid(laid) ->
        with walk = %__MODULE__{} <- presence(walk, laid, 1),
             do: {:ok, Place.slice(laid, 0, walk.shapes), Place.shifted(laid, 1), walk}

      {:node, id} ->
        {:ok, {:node, Place.read(:head, id)}, {:node, Place.read(:tail, id)},
         constrain(walk, [Ast.eq(Place.read(:tag, id), 2)])}

      _other ->
        :dead
    end
  end

  @doc "I close a record's shape or require an existing sequence to end."
  @spec ended(t(), Value.t()) :: t() | :dead
  def ended(walk, {:across, row, _address, width}),
    do: refine(walk, %{row => {:list, {0, width}, :scalar}})

  def ended(walk, value) do
    case Value.shaped(value, walk.shapes) do
      [] -> walk
      laid when Place.is_laid(laid) -> presence(walk, laid, 0)
      {:node, id} -> constrain(walk, [Ast.eq(id, 1)])
      _other -> :dead
    end
  end

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
      {"Element shapes", walk.shapes},
      {"Parameters", walk.parameters},
      {"Slots", walk.slots},
      {"Members", walk.members}
    ])
    |> ColumnedList.column("What", fn {name, _value} -> name end)
    |> ColumnedList.column("Value", fn {_name, value} -> Zkfol.Face.inspected(value) end)
    |> ColumnedList.send(fn {_name, value} -> value end)
  end
end
