defmodule Zkfol.Lay do
  @moduledoc """
  I am the lay as a value: how one allocation placed one derivation.

  ### Public API

  - `of/2`: the placement computed once.
  - `witness/1`: my matrix as the laid interpretation.
  - `claims/2`: the cells the parameters an act opens hold, by row.
  - `arrows/1`: one arrow per consumption between laid columns.
  - `addresses/1`: each address row beside the member holding it.
  - `regions/1`: the alloc's banks by name and absolute rows.
  - `at/2`: where a slot’s cell stands.
  """

  use TypedStruct

  alias Zkfol.Alloc
  alias Zkfol.Alloc.Source
  alias Zkfol.Alloc.Bank
  alias Zkfol.Alloc.Member
  alias Zkfol.Alloc.Site
  alias Zkfol.Alloc.Slot
  alias Zkfol.Ast
  alias Zkfol.Derivation
  alias Zkfol.Interpretation
  alias Zkfol.Refusal

  @typedoc "One fact standing on one member: where it stands and what its calls consumed."
  @type stand :: %{
          fact: Derivation.fact(),
          member: atom(),
          column: pos_integer(),
          uses: [use()],
          bindings: [{Slot.t(), term()}]
        }

  @typedoc "One consumption: the site that made it, and the fact it took."
  @type use :: {Site.t(), Derivation.fact()}

  @typedoc "Where a reading puts what it consumed: the column it names, or a column of its own."
  @type aim :: pos_integer() | {:free, pos_integer()}

  @typedoc "Which parameter an act opens: the head variable, or its 1-based position."
  @type parameter :: atom() | pos_integer()

  @typedoc "What an act opens: a parameter of the root or a member, or one cell of it by index."
  @type opening :: parameter() | {atom(), parameter()} | {atom(), parameter(), integer()}

  typedstruct enforce: true do
    field(:alloc, Alloc.t())
    field(:derivation, Derivation.t())
    field(:stands, [stand()])
  end

  @doc "I take the join of the derivation and alloc to form information for laying."
  @spec of(Derivation.t(), Alloc.t()) :: t()
  def of(derivation = %Derivation{}, alloc = %Alloc{members: [root | _rest]}) do
    lay = %__MODULE__{alloc: alloc, derivation: derivation, stands: []}

    case Derivation.root(derivation, root.relation) do
      nil ->
        lay

      fact ->
        index = %{
          members: Map.new(alloc.members, &{&1.name, &1}),
          clauses: Map.new(derivation.clauses),
          bindings: Map.new(derivation.bindings),
          arguments:
            Map.new(derivation.facts, fn fact = {_relation, args} ->
              {fact, List.to_tuple(args)}
            end),
          consumed:
            Map.new(derivation.consumed, fn {fact, calls} ->
              {fact,
               calls
               |> Enum.group_by(&elem(&1, 0))
               |> Map.new(fn {relation, facts} -> {relation, List.to_tuple(facts)} end)}
            end)
        }

        descend(:queue.from_list([{fact, root.name, {:free, 1}}]), lay, index, %{}, MapSet.new())
    end
  end

  @doc "I am my matrix; an unread cell pads zero, or one on an address row."
  @spec witness(t()) :: Interpretation.t()
  def witness(%__MODULE__{alloc: alloc, stands: stands}) do
    defaults = Alloc.defaults(alloc)
    positions = positions(stands, alloc)

    cells =
      Map.new(Enum.flat_map(stands, &laid(&1, alloc, positions)), fn {at, value} ->
        {at, Derivation.free_to_zero(value)}
      end)

    cells =
      case Alloc.member(alloc, Zkfol.Nodes) do
        nil -> cells
        nodes -> Zkfol.Nodes.cells(nodes, alloc, cells, defaults)
      end

    len = Enum.max([1 | for({{_row, x}, _value} <- cells, do: x)])

    Interpretation.new(
      for row <- 1..Alloc.width(alloc) do
        for x <- 1..len,
            do:
              cells
              |> Map.get({row, x}, Map.get(defaults, row, 0))
              |> Derivation.free_to_zero()
      end
    )
  end

  @doc """
  I am the cells the parameters `public` opens hold, the member's presence beside each: a
  bare parameter the root's, `{relation, parameter}` a member's, with `index` one cell.
  """
  @spec claims(t(), [opening()]) :: {:ok, [Interpretation.claim()]} | {:error, Refusal.t()}
  def claims(_lay, []), do: {:ok, []}

  def claims(lay = %__MODULE__{alloc: alloc}, public) do
    with {:ok, named} <- Refusal.flat_map(public, &opened(&1, lay)) do
      witness =
        if Enum.any?(named, &match?({_member, %Slot{allocation: {:node, _}}, _x}, &1)),
          do: witness(lay)

      named = Enum.flat_map(named, &opened_cells(&1, alloc, witness))

      {:ok,
       Enum.uniq(
         for {name, ref, x} <- named,
             {label, at} <- [{name, ref} | presence(ref, alloc)] do
           {label, Alloc.row(alloc, at), x}
         end
       )}
    end
  end

  @doc "I am one arrow per consumption between laid columns, named by the address row if any."
  @spec arrows(t()) :: [
          %{
            ptr: pos_integer() | nil,
            from_row: pos_integer(),
            from: pos_integer(),
            to: pos_integer(),
            to_row: pos_integer()
          }
        ]
  def arrows(lay = %__MODULE__{alloc: alloc}) do
    positions = positions(lay.stands, alloc)

    for stand <- lay.stands,
        {%Site{callee: callee, address: address}, _fact} = use <- stand.uses do
      %{
        ptr: Alloc.aimed(alloc, address),
        from_row: Alloc.presence(alloc, stand.member),
        from: stand.column,
        to: standing(positions, stand, use),
        to_row: Alloc.presence(alloc, callee)
      }
    end
  end

  @doc "I am each address row beside the member holding it."
  @spec addresses(t()) :: [%{ptr: pos_integer(), member: atom()}]
  def addresses(%__MODULE__{alloc: alloc}) do
    for %Member{name: name, sites: sites} <- alloc.members,
        calls <- Map.values(sites),
        %Site{address: address} <- calls,
        ptr = Alloc.aimed(alloc, address),
        uniq: true,
        do: %{ptr: ptr, member: name}
  end

  @doc "I am the alloc's regions by name, kind and absolute rows."
  @spec regions(t() | Alloc.t()) :: [
          %{name: atom(), kind: :member | :bank | :in, first: pos_integer(), last: pos_integer()}
        ]
  def regions(%__MODULE__{alloc: alloc}), do: regions(alloc)

  def regions(alloc = %Alloc{}) do
    for {name, _width} <- Alloc.regions(alloc) do
      rows = Alloc.rows(alloc, name)
      %{name: name, kind: kind(Alloc.member(alloc, name)), first: rows.first, last: rows.last}
    end
  end

  @spec kind(Member.t() | Bank.t() | Zkfol.Nodes.t() | nil) :: :in | :bank | :member
  defp kind(nil), do: :in
  defp kind(%Bank{}), do: :bank
  defp kind(%Zkfol.Nodes{}), do: :bank
  defp kind(%Alloc.Member{}), do: :member

  @doc """
  I am where the `index`-th cell of `slot`'s run stands: an address in the column
  its member stands at, which `Ast.column/2` reads as a number.
  """
  @spec at(Slot.t(), non_neg_integer()) :: Ast.address()
  def at(%Slot{allocation: {:bank, _name, {:at, base, mul, add}}}, index) do
    Ast.address(base, mul, add - index)
  end

  ############################################################
  #                   Private Implementation                 #
  ############################################################

  @spec opened(opening(), t()) ::
          {:ok, [{atom(), Slot.t(), pos_integer()}]} | {:error, Refusal.t()}
  defp opened({relation, parameter, index}, lay), do: select(relation, parameter, index, lay)

  defp opened({relation, parameter}, lay), do: select(relation, parameter, nil, lay)

  defp opened(parameter, %__MODULE__{alloc: alloc} = lay),
    do: select(Alloc.root(alloc).name, parameter, nil, lay)

  @spec select(atom(), parameter(), integer() | nil, t()) ::
          {:ok, [{atom(), Slot.t(), pos_integer()}]} | {:error, Refusal.t()}
  defp select(relation, parameter, index, %__MODULE__{alloc: alloc} = lay) do
    with {:ok, member} <-
           held(Alloc.member(alloc, relation), {:relation_not_in_scope, %{relation: relation}}),
         {:ok, slot} <-
           held(slot(member, parameter), {:unbound_variable, %{variable: parameter}}),
         {:ok, columns} <- columns(slot, member, index, lay) do
      {:ok, for(x <- columns, do: {member.name, slot, x})}
    end
  end

  @spec opened_cells({atom(), Slot.t(), pos_integer()}, Alloc.t(), Interpretation.t() | nil) ::
          [{String.t(), Ast.row_ref(), pos_integer()}]
  defp opened_cells({member, slot, x}, alloc, witness) do
    name = "#{member}.#{slot.name}"
    cells = for ref <- opening_rows(slot, member, alloc), do: {name, ref, x}

    case slot.allocation do
      {:node, ref} ->
        id = Interpretation.at(witness, Alloc.row(alloc, ref), x)
        cells ++ Zkfol.Nodes.openings(alloc, witness, id, name)

      _direct ->
        cells
    end
  end

  # The slot `parameter` names, or the one standing `parameter`-th; a bank has none to open.
  @spec slot(Member.t() | Bank.t(), parameter()) :: Slot.t() | nil
  defp slot(%Member{slots: slots}, parameter) do
    Enum.find(slots, fn slot ->
      slot.name == parameter or
        (is_integer(parameter) and slot.source == %Source{binding: {:argument, parameter - 1}})
    end)
  end

  defp slot(%Bank{}, _parameter), do: nil

  # An index spends no row; opening it opens the presence at the column.
  @spec opening_rows(Slot.t(), atom(), Alloc.t()) :: [Ast.row_ref()]
  defp opening_rows(slot, name, alloc) do
    case Alloc.slot_rows(alloc, slot) do
      [] -> [{:in, name}]
      rows -> rows
    end
  end

  @spec presence(Ast.row_ref(), Alloc.t()) :: [{String.t(), Ast.row_ref()}]
  defp presence({sym, _i}, alloc) do
    case Alloc.member(alloc, sym) do
      %Zkfol.Nodes{} -> []
      nil -> []
      _member -> [{"in", {:in, sym}}]
    end
  end

  defp presence(_ref, _alloc), do: []

  @spec held(term(), Refusal.t()) :: {:ok, term()} | {:error, Refusal.t()}
  defp held(nil, refusal), do: {:error, refusal}
  defp held(found, _refusal), do: {:ok, found}

  @spec columns(Slot.t(), Member.t(), integer() | nil, t()) ::
          {:ok, [pos_integer()]} | {:error, Refusal.t()}
  defp columns(%Slot{allocation: {:bank, _, _}}, _member, index, _lay) when is_integer(index),
    do: {:ok, [index + 1]}

  defp columns(_slot, %Member{name: name, steps: steps}, index, _lay) when is_integer(index) do
    with {:ok, {_j, origin}} <- held(steps, {:beyond_the_rows, %{relation: name}}),
         do: {:ok, [index - origin]}
  end

  defp columns(%Slot{allocation: {:bank, bank, _}} = slot, member, nil, lay) do
    with {:ok, {cells, x}} <-
           held(bank_values(slot, member, lay), {:beyond_the_rows, %{sequence: bank}}),
         do: {:ok, for(p <- (length(cells) - 1)..0//-1, do: Ast.column(at(slot, p), x))}
  end

  defp columns(_slot, %Member{name: name}, nil, %__MODULE__{stands: stands}) do
    stood = Enum.find(stands, &(&1.member == name))

    with {:ok, %{fact: fact}} <- held(stood, {:beyond_the_rows, %{relation: name}}),
         do:
           {:ok, for(stand <- stands, stand.member == name, stand.fact == fact, do: stand.column)}
  end

  @spec bank_values(Slot.t(), Member.t(), t()) :: {[term()], pos_integer()} | nil
  defp bank_values(slot, %Member{name: name}, %__MODULE__{} = lay) do
    with %{bindings: bindings, column: x} <- Enum.find(lay.stands, &(&1.member == name)),
         {^slot, cells} when is_list(cells) <- List.keyfind(bindings, slot, 0),
         do: {cells, x},
         else: (_unheld -> nil)
  end

  @spec descend(:queue.queue(), t(), map(), map(), MapSet.t()) :: t()
  defp descend(queue, lay, index, occupied, seen) do
    case :queue.out(queue) do
      {:empty, _queue} ->
        %{lay | stands: Enum.reverse(lay.stands)}

      {{:value, {{_relation, tuple} = fact, name, aim}}, rest} ->
        member = index.members[name]
        {column, taken} = placed(aim, member, tuple, Map.get(occupied, name, %{}))
        key = {name, fact, column}

        if MapSet.member?(seen, key) do
          descend(rest, lay, index, occupied, seen)
        else
          calls = Map.get(member.sites, Map.get(index.clauses, fact), [])

          uses =
            for site <- calls,
                took <- consumed(site.source, fact, index.consumed),
                do: {site, took}

          bindings =
            for slot = %Slot{source: source = %Source{}} <- member.slots,
                source.clause == nil or source.clause == index.clauses[fact],
                took <- consumed(source.calls, fact, index.consumed),
                do: {slot, source_value(source.binding, took, index)}

          stand = %{fact: fact, member: name, column: column, uses: uses, bindings: bindings}
          {next, taken} = vacant(column + 1, taken)
          occupied = Map.put(occupied, name, Map.put(taken, column, next))

          queue =
            Enum.reduce(uses, rest, fn {%Site{callee: callee, address: address}, took}, q ->
              :queue.in({took, callee, aimed(address, column)}, q)
            end)

          descend(
            queue,
            %{lay | stands: [stand | lay.stands]},
            index,
            occupied,
            MapSet.put(seen, key)
          )
        end
    end
  end

  @spec source_value(
          {:argument, non_neg_integer()} | {:variable, atom()},
          Derivation.fact(),
          map()
        ) :: term()
  defp source_value({:argument, k}, fact, index), do: elem(index.arguments[fact], k)
  defp source_value({:variable, name}, fact, index), do: Map.fetch!(index.bindings[fact], name)

  # A call's source path follows the derivation through any wrappers that were inlined.
  @spec consumed([{atom(), non_neg_integer()}], Derivation.fact(), map()) :: [Derivation.fact()]
  defp consumed([], fact, _index), do: [fact]

  defp consumed([{relation, occurrence} | rest], fact, index) do
    calls = index |> Map.get(fact, %{}) |> Map.get(relation, {})

    if occurrence < tuple_size(calls),
      do: consumed(rest, elem(calls, occurrence), index),
      else: []
  end

  @spec positions([stand()], Alloc.t()) :: map()
  defp positions(stands, alloc) do
    pointed =
      for %Member{sites: sites} <- alloc.members,
          calls <- Map.values(sites),
          %Site{callee: callee, address: {:at, {:cell, _ptr}, _mul, _add}} <- calls,
          into: MapSet.new(),
          do: callee

    for stand <- Enum.reverse(stands),
        MapSet.member?(pointed, stand.member),
        into: %{},
        do: {{stand.member, stand.fact}, stand.column}
  end

  @spec aimed(Ast.address(), pos_integer()) :: aim()
  defp aimed({:at, :x, _mul, _add} = address, column), do: Ast.column(address, column)
  defp aimed({:at, {:cell, _ptr}, _mul, _add}, column), do: {:free, column}

  # A fact two sites consumed stands under each, at the column each names.
  @spec standing(map(), stand(), use()) :: pos_integer()
  defp standing(positions, stand, {%Site{callee: callee, address: address}, fact}) do
    with {:free, _near} <- aimed(address, stand.column),
         do: Map.get(positions, {callee, fact}, 1)
  end

  # A fact no site addressed stands where its steps put its count, else at a vacant column.
  @spec placed(aim(), Member.t(), [term()], map()) :: {pos_integer(), map()}
  defp placed(column, _member, _tuple, taken) when is_integer(column), do: {column, taken}

  defp placed({:free, near}, %Member{steps: steps}, tuple, taken) do
    with {j, origin} <- steps,
         count when is_integer(count) <- count_of(Enum.at(tuple, j)),
         do: {count - origin, taken},
         else: (_uncounted -> vacant(near, taken))
  end

  @spec count_of(term()) :: integer() | nil
  defp count_of(q) when is_integer(q), do: q
  defp count_of(cells) when is_list(cells), do: length(cells)
  defp count_of(_open), do: nil

  # Each occupied position points toward a vacancy; searches compress the traversed path.
  @spec vacant(pos_integer(), map()) :: {pos_integer(), map()}
  defp vacant(column, used) do
    case Map.fetch(used, column) do
      :error ->
        {column, used}

      {:ok, next} ->
        {free, used} = vacant(next, used)
        {free, Map.put(used, column, free)}
    end
  end

  @spec laid(stand(), Alloc.t(), map()) :: [{{pos_integer(), pos_integer()}, term()}]
  defp laid(stand = %{member: name, column: x}, alloc, positions) do
    chosen =
      for {%Site{address: address}, _fact} = use <- stand.uses,
          row = Alloc.aimed(alloc, address),
          do: {{row, x}, standing(positions, stand, use)}

    [{{Alloc.presence(alloc, name), x}, 1}] ++
      Enum.flat_map(stand.bindings, &spread(&1, x, alloc)) ++ chosen
  end

  # The allocation determines placement: scalar, term identity, bank, or no storage.
  @spec spread({Slot.t(), term()}, pos_integer(), Alloc.t()) ::
          [{{pos_integer(), pos_integer()}, term()}]
  # A closure is {method, object, fixed arguments...}; the fixed arguments go to the rows.
  defp spread({%Slot{allocation: {:rel, _name, rows}}, closure}, x, alloc) do
    fixed = closure |> Tuple.to_list() |> Enum.drop(2)
    for {value, row} <- Enum.zip(fixed, rows), do: {{Alloc.row(alloc, row), x}, value}
  end

  defp spread({%Slot{allocation: {:cell, ref}}, value}, x, alloc),
    do: [{{Alloc.row(alloc, ref), x}, value}]

  defp spread({%Slot{allocation: {:node, ref}}, value}, x, alloc),
    do: [{{Alloc.row(alloc, ref), x}, {:node, value}}]

  defp spread({slot = %Slot{allocation: {:bank, bank, _address}}, values}, x, alloc)
       when is_list(values) do
    rows = Alloc.slot_rows(alloc, slot)

    suffix_rows =
      for ref = {Zkfol.Nodes, {:suffix, {^bank, _element}}} <- Alloc.refs(alloc),
          do: Alloc.row(alloc, ref)

    Enum.flat_map(Enum.with_index(values), fn {value, p} ->
      column = Ast.column(at(slot, p), x)

      cells =
        for {cell, row} <- Enum.zip(row_values(value, length(rows)), rows),
            do: {{Alloc.row(alloc, row), column}, cell}

      nodes = for row <- suffix_rows, do: {{row, column}, {:node, Enum.drop(values, p)}}
      [{{Alloc.presence(alloc, bank), column}, 1} | cells ++ nodes]
    end)
  end

  defp spread(_unallocated, _x, _alloc), do: []

  # An inner bracket is an earlier dimension, so its cells run onto rows first.
  @spec row_values(term(), non_neg_integer()) :: [term()]
  defp row_values(_cells, 0), do: []
  defp row_values([], k), do: List.duplicate(0, k)
  defp row_values([cell | tail], k) when is_list(cell), do: row_values(cell ++ tail, k)
  defp row_values([head | tail], k), do: [head | row_values(tail, k - 1)]
  defp row_values(cell, 1), do: [cell]
  defp row_values(_ended, k), do: List.duplicate(0, k)
end

defimpl Inspect, for: Zkfol.Lay do
  import Inspect.Algebra

  def inspect(lay = %Zkfol.Lay{}, _opts) do
    regions =
      Enum.map_join(Zkfol.Lay.regions(lay), " ", fn %{name: name, first: first, last: last} ->
        "#{name}:#{first}-#{last}"
      end)

    concat([
      "#Zkfol.Lay<",
      "#{Enum.max([1 | for(stand <- lay.stands, do: stand.column)])} columns · #{regions}",
      ">"
    ])
  end
end
