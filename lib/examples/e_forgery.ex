defmodule Examples.EForgery do
  @moduledoc """
  I am the oracle swept over the corpus: every cell of every witness moved on its own,
  every believed move weighed against what the predicate leaves open.
  """

  use ExExample

  import ExUnit.Assertions

  alias Examples.EAl
  alias Examples.EAst
  alias Examples.EDoubling
  alias Examples.EFacts
  alias Examples.ENodes
  alias Examples.EPassed
  alias Examples.EPhi
  alias Examples.EUser
  alias Zkfol.Alloc
  alias Zkfol.Alloc.Slot
  alias Zkfol.Ast
  alias Zkfol.Interpretation
  alias Zkfol.Lay
  alias Zkfol.Lang.Rel
  alias Zkfol.Log
  alias Zkfol.Semantics
  alias Zkfol.Statement

  @typedoc "One cell moved: where it sits, what it held, and what it took."
  @type move :: {{pos_integer(), pos_integer()}, integer(), integer()}

  @typedoc "One read of one cell: an equality value, a domain bound, or a pointer address."
  @type deref :: {:value | :address | :bound, {pos_integer(), integer() | :error}}

  @typedoc "One reading: the column that made it, and the standing its conjunct speaks for."
  @type reader :: {pos_integer(), pos_integer() | nil}

  @doc "I am every statement the sweep runs over: one of every shape the corpus writes."
  @spec statements() :: [{atom(), Statement.t()}]
  example statements do
    [
      fib: EUser.fibonacci(),
      regs: EUser.registers(),
      power: EUser.power(),
      paired: EUser.shared_index(),
      doubled: EUser.doubles(),
      reshaped: emitted(EUser.both(), [[1, 2, 3], :_]),
      twice_read: emitted(EUser.twice_read(), [[1, 2, 3], :_]),
      chained: EUser.chained_walks(),
      handed: EUser.strided_handoff(),
      tacked: EUser.tacked_bank(),
      indexed: EUser.indexed_cell(),
      mapped: emitted(EUser.bumped(), [:_]),
      appended: emitted(EUser.joined(), [[1, 2], [3, 4], :_]),
      remainder: emitted(EUser.dropped(), [3, [1, 2, 3, 4], :_]),
      zero_based: EUser.zero_based(),
      row_sums: EUser.row_sums(),
      diagonal: emitted(EUser.diagonal(), [[[3, 4], [5, 6]], :_]),
      kernel: EDoubling.rewritten_fibonacci(),
      doubled_fun: emitted(EUser.doubled_fun(), [[1, 2, 3], :_]),
      hop: emitted(EAl.hop_rel(), [5]),
      pick: emitted([EAl.pick(), EAl.tab()], [:_, 41]),
      capped: emitted(EAl.capped(), [2]),
      mod: emitted(EAl.regsm(), [10]),
      forked: emitted(EAl.forked(), [2, 10]),
      parities: emitted([EAl.odd(), EAl.even()], [5, :_]),
      aimed: emitted([EAl.summed(), EAl.both()], [1, :_]),
      factorial: emitted(EFacts.factorial(), [5]),
      local_factor: EPhi.factored(),
      local_calls: EPhi.factored_pair(),
      repeated_calls: EPhi.repeated_factors(),
      wrapped: EPhi.wrapped(),
      divided: EPhi.divided(),
      aliased: EPhi.aliased(),
      construction: EPhi.construction(),
      alternative: EPhi.selected_alternative(),
      first_row: EPassed.first_row(),
      picked_row: EPassed.picked_row(),
      strided_last: EPassed.strided_last(),
      mutual_last: EPassed.mutual_last(),
      loose_last: EPassed.loosely_stepped(),
      last_at: EPassed.agreeing_bases(),
      optional_tail: ENodes.scalar_tail()
    ]
  end

  @doc "I am every move the oracle believed, beside the facts only the openings pin."
  @spec freedoms() :: [{atom(), [move()], [move()]}]
  example freedoms do
    for {name, statement} <- statements() do
      pred = Statement.pred(statement)
      witness = Statement.witness(statement)
      assert Semantics.valid?(pred, witness), "#{name} is no witness of its own predicate"

      {believed, surprising} = sweep(statement)
      assert surprising == [], "#{name} moves unaccounted for: #{inspect(surprising)}"

      absences = claimed(statement)
      assert absences != [], "#{name} leaves no fact to its openings"
      assert Enum.all?(absences, &(&1 in believed)), "#{name} refuses an absence its claim pins"
      {name, absences, believed}
    end
  end

  @doc "I am the placing checked: every cell of every sequence read back where its reader looks."
  @spec placings() :: [{atom(), non_neg_integer()}]
  example placings do
    counts =
      for {name, statement} <- statements() do
        read = placing(statement)

        assert Enum.all?(read, fn {cell, at} -> at == {:ok, cell} end),
               "#{name} lays a sequence it does not hold: #{inspect(read)}"

        {name, length(read)}
      end

    assert Enum.any?(counts, fn {_name, count} -> count > 0 end),
           "placement checks examined no bank cells"

    counts
  end

  @doc "I am one witness swept: the moves the oracle believed, and the moves it should not have."
  @spec sweep(Statement.t()) :: {[move()], [move()]}
  def sweep(statement = %Statement{}) do
    pred = Statement.pred(statement)
    witness = Statement.witness(statement)
    read = read(pred, witness)
    bits = presence(statement)
    pins = MapSet.new(claimed(statement))

    free = freed(statement)
    private = private(statement)

    spelt =
      MapSet.new(
        for {held, seq, i, x} <- data(statement),
            is_integer(held),
            seq not in free,
            do: {i, x}
      )

    graded =
      for {i, x} = cell <- cells(witness),
          from = Interpretation.at(witness, i, x),
          to <- moves(from, i in bits),
          move = {cell, from, to},
          forged = EAst.tamper(witness, i, x, to) do
        # The predicate judges everywhere: the read index can miss a column a move breaks.
        believed = Semantics.valid?(pred, forged)

        accounted =
          cond do
            cell in private -> true
            from == 1 and to == 0 and i in bits -> move in pins
            true -> unread?(move, spelt, read, pred, witness)
          end

        {move, believed, accounted}
      end

    # A forgery is a believed move the design never declared free; the converse is strictness.
    {for({move, true, true} <- graded, do: move), for({move, true, false} <- graded, do: move)}
  end

  @doc "I am the facts a statement leaves to its openings: those no other column reads."
  @spec claimed(Statement.t()) :: [move()]
  def claimed(statement = %Statement{}) do
    alloc = Statement.alloc(statement)
    witness = Statement.witness(statement)
    read = read(Statement.pred(statement), witness)

    for i <- Enum.uniq(standing(alloc)),
        x <- 1..Interpretation.len(witness),
        Interpretation.at(witness, i, x) == 1,
        readers = Map.get(read, {:value, {i, x}}, []) ++ Map.get(read, {:bound, {i, x}}, []),
        Enum.all?(readers, &(&1 == {x, i})),
        do: {{i, x}, 1, 0}
  end

  @doc "I am one witness's placing: each cell of a sequence beside what stands where it is read."
  @spec placing(Statement.t()) :: [{integer(), {:ok, integer()} | :error}]
  def placing(statement) do
    witness = Statement.witness(statement)
    for {held, _seq, i, x} <- data(statement), do: {held, Interpretation.fetch(witness, i, x)}
  end

  ############################################################
  #                   Private Implementation                 #
  ############################################################

  @spec moves(integer(), boolean()) :: [integer()]
  defp moves(1, true), do: [2, -1, 0]
  defp moves(_from, true), do: [2, -1]
  defp moves(from, false), do: [from + 1, from - 1]

  @spec unread?(move(), MapSet.t(), map(), Ast.pred(), Interpretation.t()) :: boolean()
  defp unread?({{i, _x} = cell, from, to}, spelt, read, pred, witness) do
    cell not in spelt and not is_map_key(read, {:value, cell}) and
      (not is_map_key(read, {:address, cell}) or twin?(pred, witness, i, from, to))
  end

  @spec data(Statement.t()) :: [{term(), atom(), pos_integer(), integer()}]
  defp data(statement) do
    lay = Statement.lay(statement)
    alloc = Statement.alloc(statement)

    for stand <- lay.stands,
        {_relation, tuple} = stand.fact,
        {value, slot = %Slot{allocation: {:bank, bank, _extent}}} <-
          Enum.zip(tuple, Alloc.member(alloc, stand.member).slots),
        is_list(value),
        {cell, p} <- Enum.with_index(value),
        column = Ast.column(Lay.at(slot, p), stand.column),
        {held, ref} <- Enum.zip(List.flatten([cell]), Alloc.slot_rows(alloc, slot)),
        do: {held, bank, Alloc.row(alloc, ref), column}
  end

  # A sequence the act handed no datum holds the run's answer, which nothing need read back.
  @spec freed(Statement.t()) :: [atom()]
  defp freed(statement = %Statement{args: args}) do
    [root | _rest] = Statement.alloc(statement).members

    for {:_, %Slot{allocation: {:bank, owner, _extent}}} <-
          Enum.zip(args, root.slots),
        do: owner
  end

  # A value the act handed but did not open is a private witness: free, never a forgery.
  @spec private(Statement.t()) :: MapSet.t()
  defp private(statement = %Statement{args: args}) do
    lay = Statement.lay(statement)
    arguments = for {arg, k} <- Enum.with_index(args, 1), arg != :_, do: k
    {:ok, claims} = Lay.claims(lay, arguments)
    standing = presence(statement)

    MapSet.new(for {_name, i, x} <- claims, i not in standing, do: {i, x})
  end

  @spec read(Ast.pred(), Interpretation.t()) :: %{deref() => [reader()]}
  defp read(pred, witness) do
    for conjunct <- Ast.conjuncts(pred),
        owner <- [owner(conjunct)],
        x <- 1..Interpretation.len(witness),
        {_kind, cell} = deref <- reads(conjunct, witness, x),
        inside?(witness, cell),
        reduce: %{} do
      seen -> Map.update(seen, deref, [{x, owner}], &[{x, owner} | &1])
    end
  end

  # A member says where it stands before it says anything else.
  @spec owner(Ast.pred()) :: pos_integer() | nil
  defp owner({:disj, [absent | _rest]}) do
    case Ast.conjuncts(absent) do
      [{:eq, {:cell, i}, 0}] -> i
      _conditional -> nil
    end
  end

  defp owner(_conjunct), do: nil

  @spec reads(Ast.pred() | Ast.term_t(), Interpretation.t(), pos_integer()) :: MapSet.t(deref())
  defp reads({:conj, preds}, witness, x), do: preds |> Enum.map(&reads(&1, witness, x)) |> union()

  defp reads({:disj, preds}, witness, x) do
    case Enum.filter(preds, &Semantics.holds?(&1, witness, x)) do
      [] ->
        preds |> Enum.map(&reads(&1, witness, x)) |> union()

      answering ->
        answering |> Enum.map(&reads(&1, witness, x)) |> Enum.reduce(&MapSet.intersection/2)
    end
  end

  defp reads({tag, t, u}, witness, x) when tag in [:eq, :add],
    do: union([reads(t, witness, x), reads(u, witness, x)])

  defp reads({:mul, t, u}, witness, x) do
    union([
      if(Semantics.eval(u, witness, x) == 0, do: MapSet.new(), else: reads(t, witness, x)),
      if(Semantics.eval(t, witness, x) == 0, do: MapSet.new(), else: reads(u, witness, x))
    ])
  end

  # A domain check reads a value without fixing it: moving within the domain is allowed.
  defp reads({:natural, t}, witness, x) do
    MapSet.new(reads(t, witness, x), fn
      {:value, cell} -> {:bound, cell}
      address -> address
    end)
  end

  defp reads(leaf, witness, x), do: MapSet.new(derefs(leaf, witness, x))

  @spec derefs(Ast.pred() | Ast.term_t(), Interpretation.t(), pos_integer()) :: [deref()]
  defp derefs(node, witness, x) do
    Ast.reduce(node, [], fn node, seen ->
      case Ast.read(node) do
        {i, {:at, base, _mul, _add} = address} ->
          [{:value, {i, Semantics.column(address, witness, x)}} | aimed(base, x)] ++ seen

        nil ->
          seen
      end
    end)
  end

  @spec aimed(Ast.address_base(), pos_integer()) :: [deref()]
  defp aimed({:cell, j}, x), do: [{:address, {j, x}}]
  defp aimed(:x, _x), do: []

  @spec standing(Alloc.t()) :: [pos_integer()]
  defp standing(alloc = %Alloc{}) do
    root = Alloc.root(alloc)

    banks =
      for %Slot{allocation: {:bank, owner, _extent}} <- root.slots,
          do: owner

    for name <- [root.name | banks], do: Alloc.presence(alloc, name)
  end

  @spec presence(Statement.t()) :: [pos_integer()]
  defp presence(statement = %Statement{}) do
    alloc = Statement.alloc(statement)
    for {:in, _name} = ref <- Alloc.refs(alloc), do: Alloc.row(alloc, ref)
  end

  # A pointer moved is aimed elsewhere: every reading through it must meet the same value.
  @spec twin?(Ast.pred(), Interpretation.t(), pos_integer(), integer(), integer()) :: boolean()
  defp twin?(pred, witness, j, from, to) do
    through = through(pred, j)

    through != [] and inside?(witness, {1, to}) and
      Enum.all?(through, &(Semantics.eval(&1, witness, from) == Semantics.eval(&1, witness, to)))
  end

  @spec through(Ast.pred(), pos_integer()) :: [Ast.term_t()]
  defp through(pred, j) do
    Ast.reduce(pred, [], fn node, seen ->
      case Ast.read(node) do
        {i, {:at, {:cell, ^j}, mul, add}} -> [Ast.at(i, :x, mul, add) | seen]
        _other -> seen
      end
    end)
    |> Enum.uniq()
  end

  @spec cells(Interpretation.t()) :: [{pos_integer(), pos_integer()}]
  defp cells(witness) do
    for i <- 1..Interpretation.arity(witness), x <- 1..Interpretation.len(witness), do: {i, x}
  end

  @spec inside?(Interpretation.t(), {pos_integer(), integer() | :error}) :: boolean()
  defp inside?(witness, {i, x}) do
    is_integer(x) and x in 1..Interpretation.len(witness)//1 and
      i in 1..Interpretation.arity(witness)//1
  end

  @spec union([MapSet.t(cell)]) :: MapSet.t(cell) when cell: var
  defp union([]), do: MapSet.new()
  defp union(sets), do: Enum.reduce(sets, &MapSet.union/2)

  @spec emitted(Rel.t() | [Rel.t()], [Statement.datum() | :_]) :: Statement.t()
  defp emitted(rels, args), do: Log.Run.final_stage(Zkfol.emit(rels, args: args))
end
