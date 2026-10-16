defmodule Zkfol.Uair do
  @moduledoc "I am the UAIR of a statement: Figure 2 over committed columns."

  use TypedStruct

  import Bitwise

  alias Zkfol.Ast
  alias Zkfol.Interpretation
  alias Zkfol.Refusal
  alias Zkfol.Semantics
  alias Zkfol.Uair.Composed
  alias Zkfol.Uair.Plain
  alias Zkfol.ZincPlus

  @typedoc "A UAIR is plain, or is a Section 4 lowering."
  @type mode :: Plain.t() | Composed.t()

  @typedoc "One composed read: where the address bits live and where the dereference lands."
  @type read :: %{
          row: non_neg_integer(),
          value_row: non_neg_integer(),
          bit_rows: [non_neg_integer()],
          result_row: non_neg_integer()
        }

  @typedoc "A cell of the trace: its row and its column."
  @type cell :: {pos_integer(), pos_integer()}

  @typedoc "A row of the committed columns: a witness row, the column index, or the ones."
  @type row :: pos_integer() | :x | :ones

  @typedoc """
  What a read is to the program: a shift back, a pointer through a row, a tie to a cell
  named by its column, or aimed at an address no shift reaches.
  """
  @type kind ::
          {:shift, non_neg_integer()}
          | :pointer
          | {:tie, cell()}
          | {:aimed, Ast.address()}

  @typedoc """
  One op of the program. `up c` pushes column c at the row; `down i` pushes the column
  of the i-th shift, that shift's rows on; `const` pushes; `add` and `mul` pop two and
  push.
  """
  @type op ::
          {:up, non_neg_integer()}
          | {:down, non_neg_integer()}
          | {:const, integer()}
          | :add
          | :mul

  @typedoc "A column the program reads back, and by how many rows."
  @type shift :: {non_neg_integer(), pos_integer()}

  # A bounded row is spelled in limbs the backend's Word table ranges over.
  @limb_width 8
  @limbs 4

  typedstruct enforce: true do
    field(:num_public, non_neg_integer())
    # Columns past `len` are padding.
    field(:len, pos_integer())
    field(:claims, [{String.t(), non_neg_integer()}], default: [])
    field(:shifts, [shift()])
    field(:program, [op()])
    field(:degree, non_neg_integer())
    field(:columns, [[integer()]])
    field(:mode, mode(), default: %Plain{})
    field(:rows, [row()], default: [])
    # A bounded column and the columns of its limbs.
    field(:limbs, [{non_neg_integer(), [non_neg_integer()]}], default: [])
    field(:selected_lookups, [ZincPlus.Selected.t()], default: [])
    field(:permuted_lookups, [ZincPlus.Permuted.t()], default: [])
    field(:point_ties, [ZincPlus.Tie.t()], default: [])
  end

  @doc "I am the Word lookups the limbs owe: one per limb column, over the limb width."
  @spec word_lookups(t()) :: [ZincPlus.lookup()]
  def word_lookups(%__MODULE__{limbs: limbs}),
    do: for({_column, columns} <- limbs, column <- columns, do: {column, @limb_width})

  @doc "I am the committed column count: the columns themselves say it."
  @spec num_cols(t()) :: non_neg_integer()
  def num_cols(%__MODULE__{columns: columns}), do: length(columns)

  @doc "I am the cube’s width: covering `len` plus an exempt padding row, never under three."
  @spec num_vars(t() | pos_integer()) :: pos_integer()
  def num_vars(%__MODULE__{len: len}), do: num_vars(len)
  def num_vars(len) when is_integer(len), do: max(length(Integer.digits(len, 2)), 3)

  @doc "I run the program at one row of the cube."
  @spec evaluate(t(), non_neg_integer()) :: integer()
  def evaluate(uair = %__MODULE__{program: program}, row) do
    program
    |> Enum.reduce([], &step(&1, &2, uair, row))
    |> hd()
  end

  @spec step(op(), [integer()], t(), non_neg_integer()) :: [integer()]
  defp step({:const, k}, stack, _, _), do: [k | stack]
  defp step(:add, [b, a | stack], _, _), do: [a + b | stack]
  defp step(:mul, [b, a | stack], _, _), do: [a * b | stack]
  defp step({:up, col}, stack, uair, row), do: [cell(uair, col, row) | stack]

  defp step({:down, i}, stack, uair = %__MODULE__{shifts: shifts}, row) do
    {col, back} = Enum.at(shifts, i)
    [cell(uair, col, row + back) | stack]
  end

  # Past the end of the cube a column reads zero.
  @spec cell(t(), non_neg_integer(), non_neg_integer()) :: integer()
  defp cell(%__MODULE__{columns: columns}, col, row),
    do: columns |> Enum.at(col) |> Enum.at(row, 0)

  @doc "I hold when the program is zero at every row of the cube but the exempt last."
  @spec holds?(t()) :: boolean()
  def holds?(uair = %__MODULE__{}) do
    Enum.all?(0..((1 <<< num_vars(uair)) - 2), &(evaluate(uair, &1) == 0))
  end

  @doc """
  I translate a statement into what Zinc+ proves: the witness as committed columns with
  the claimed rows first, the program over them, and the lookups. The witness grows a
  row for every term the program cannot read directly.
  """
  @spec emit(Ast.pred(), Interpretation.t(), [Interpretation.claim()]) ::
          {:ok, t()} | {:error, Refusal.t()}
  def emit(pred, witness, claims \\ []) do
    len = Interpretation.len(witness)
    public = for {_name, i, _c} <- claims, uniq: true, do: i

    with {:ok, values} <- claimed(claims, witness),
         :ok <- models(pred, witness),
         pred = guarded(pred, len),
         {pred, witness} = sorted_copies({pred, witness}) |> bounded_expressions(),
         obligations = obligations(pred),
         named = Enum.flat_map(obligations, &Ast.reads/1),
         {:ok, tables} <- tables(obligations, len),
         {:ok, pairs} <- pairs(obligations, len),
         {:ok, witness} <- filled(witness, tables, claims),
         {pred, witness, ties} = named_cells(stripped(pred), witness),
         pointed = Enum.flat_map(Ast.pointer_derefs(pred), &Tuple.to_list/1),
         {pred, witness, public} = twinned(pred, witness, public, pointed ++ named),
         {:ok, pred, witness, lowering} <- Composed.lower(pred, witness, num_vars(len)),
         bounded = naturals(obligations) ++ Composed.bounded_rows(lowering),
         {pred, witness, limbs} = limbed(pred, witness, bounded),
         poly = polynomial(pred, len),
         unread = named ++ Composed.value_rows(lowering) ++ Enum.map(ties, &elem(&1, 0)),
         rows = layout(poly, public, unread),
         cols = rows |> Enum.with_index() |> Map.new(),
         shifts = shifts(poly, cols),
         program = ops(poly, cols, shifts),
         columns = columns(witness, rows),
         :ok <- ZincPlus.fits(columns),
         :ok <- ZincPlus.constants_fit(program) do
      {:ok,
       %__MODULE__{
         num_public: length(public),
         len: len,
         claims: values,
         shifts: shifts,
         program: program,
         degree: Ast.degree(pred),
         columns: columns,
         mode: Composed.emitted(lowering, cols),
         rows: rows,
         limbs: for({row, rows} <- limbs, do: {cols[row], Enum.map(rows, &cols[&1])}),
         selected_lookups: selected(tables, cols, len),
         permuted_lookups: permuted(pairs, cols, len),
         point_ties:
           for {i, c, row} <- ties do
             %ZincPlus.Tie{column: cols[i], row: len - c, target: {:broadcast, cols[row]}}
           end
       }}
    end
  end

  ############################################################
  #                         The rows                         #
  ############################################################

  @spec rowed(Interpretation.t(), [leaf], (leaf, pos_integer() -> integer())) ::
          {Interpretation.t(), %{leaf => pos_integer()}}
        when leaf: var
  defp rowed(witness, leaves, value) do
    columns = 1..Interpretation.len(witness)
    rows = Enum.map(leaves, fn leaf -> Enum.map(columns, &value.(leaf, &1)) end)

    {Interpretation.new(Interpretation.rows(witness) ++ rows),
     Map.new(Enum.with_index(leaves, Interpretation.arity(witness) + 1))}
  end

  # A permuted lookup proves the copy is the same multiset, and a natural between each
  # neighbour proves it is strictly sorted, so the cells are distinct.
  @spec sorted_copies({Ast.pred(), Interpretation.t()}) :: {Ast.pred(), Interpretation.t()}
  defp sorted_copies({pred, witness}) do
    groups = for {:distinct, cells} <- obligations(pred), do: cells

    ranks =
      Enum.flat_map(groups, fn cells -> Enum.map(0..(length(cells) - 1)//1, &{cells, &1}) end)

    {witness, rows} = rowed(witness, ranks, &sorted_value(&1, witness, &2))
    copy = fn cells -> for {^cells, k} <- ranks, do: Ast.cell(rows[{cells, k}]) end

    pred =
      Ast.postwalk(pred, fn
        {:distinct, cells} ->
          Ast.conj([Ast.permuted(cells, copy.(cells)) | ascending(copy.(cells))])

        node ->
          node
      end)

    {pred, witness}
  end

  # Each neighbour exceeds the last by at least one.
  @spec ascending([Ast.term_t()]) :: [Ast.pred()]
  defp ascending(copy) do
    copy
    |> Enum.chunk_every(2, 1, :discard)
    |> Enum.map(fn [a, b] -> Ast.natural(Ast.sub(Ast.sub(b, a), 1)) end)
  end

  # A cell read off the trace leaves the copy at 0; the lookup then fails, as it should.
  @spec sorted_value({[Ast.term_t()], non_neg_integer()}, Interpretation.t(), pos_integer()) ::
          integer()
  defp sorted_value({cells, k}, witness, x) do
    values = Enum.map(cells, &Semantics.eval(&1, witness, x))
    if :error in values, do: 0, else: values |> Enum.sort() |> Enum.at(k)
  end

  # The Word lookup ranges over a column, so a bounded expression needs one.
  @spec bounded_expressions({Ast.pred(), Interpretation.t()}) ::
          {Ast.pred(), Interpretation.t()}
  defp bounded_expressions({pred, witness}) do
    terms = for {:natural, t} <- obligations(pred), Ast.read(t) == nil, do: t
    {witness, rows} = rowed(witness, terms, &natural_value(&1, witness, &2))

    pred =
      Ast.postwalk(pred, fn
        {:natural, t} when is_map_key(rows, t) ->
          Ast.conj([Ast.eq(Ast.cell(rows[t]), t), Ast.natural(Ast.cell(rows[t]))])

        node ->
          node
      end)

    {pred, witness}
  end

  # The Word table ranges over a limb, so a bounded row is spelled in limbs. The program
  # skips the cube's last row, so the spelling is stated a row back too, which holds it
  # there as well.
  @spec limbed(Ast.pred(), Interpretation.t(), [pos_integer()]) ::
          {Ast.pred(), Interpretation.t(), [{pos_integer(), [pos_integer()]}]}
  defp limbed(pred, witness, bounded) do
    bounded = Enum.uniq(bounded)
    leaves = for row <- bounded, k <- 0..(@limbs - 1), do: {row, k}
    {witness, rows} = rowed(witness, leaves, &limb(&1, witness, &2))
    limbs = for row <- bounded, do: {row, Enum.map(0..(@limbs - 1), &rows[{row, &1}])}

    spellings =
      for {row, limb_rows} <- limbs, back <- [0, -1] do
        weighted =
          limb_rows
          |> Enum.with_index()
          |> Enum.map(fn {l, k} -> Ast.mul(Ast.at(l, :x, 1, back), 1 <<< (@limb_width * k)) end)

        Ast.eq(Ast.at(row, :x, 1, back), Enum.reduce(weighted, &Ast.add(&2, &1)))
      end

    pred =
      pred
      |> Ast.branches()
      |> Enum.map(&Ast.conj(Ast.conjuncts(&1) ++ spellings))
      |> Ast.disj()

    {pred, witness, limbs}
  end

  @spec limb({pos_integer(), non_neg_integer()}, Interpretation.t(), pos_integer()) ::
          integer()
  defp limb({row, k}, witness, x),
    do: Interpretation.at(witness, row, x) >>> (@limb_width * k) &&& (1 <<< @limb_width) - 1

  @spec natural_value(Ast.term_t(), Interpretation.t(), pos_integer()) :: non_neg_integer()
  defp natural_value(term, witness, x) do
    with v when is_integer(v) and v >= 0 <- Semantics.eval(term, witness, x),
         do: v,
         else: (_ -> 0)
  end

  # The program reads only the current column and shifts back. A read at a fixed column
  # becomes a row holding that value, tied to the cell. A read at any other address
  # becomes a pointer row holding the column, equated to the address inside the
  # conjunction that reads it, since on other branches the address may leave the trace.
  @spec named_cells(Ast.pred(), Interpretation.t()) ::
          {Ast.pred(), Interpretation.t(), [{pos_integer(), pos_integer(), pos_integer()}]}
  defp named_cells(pred, witness) do
    len = Interpretation.len(witness)

    leaves =
      reads(pred)
      |> Enum.map(&kind(&1, len))
      |> Enum.filter(&match?({tag, _} when tag in [:tie, :aimed], &1))
      |> Enum.uniq()
      |> Enum.sort()

    {witness, rows} = rowed(witness, leaves, &held(&1, witness, &2, len))
    aimed = for {{:aimed, address}, row} <- rows, into: %{}, do: {row, address}

    pred =
      Ast.postwalk(pred, fn
        {:conj, parts} ->
          {:conj, parts ++ pins(parts, aimed)}

        node ->
          with {i, _address} = read <- Ast.read(node),
               leaf when is_map_key(rows, leaf) <- kind(read, len) do
            case leaf do
              {:tie, _cell} -> Ast.cell(rows[leaf])
              {:aimed, _address} -> Ast.cell(i, rows[leaf])
            end
          else
            _in_place -> node
          end
      end)

    ties = for {{:tie, {i, c}}, row} <- rows, do: {i, c, row}
    {pred, witness, ties}
  end

  @spec held(kind(), Interpretation.t(), pos_integer(), pos_integer()) :: integer()
  defp held({:tie, {i, c}}, witness, _x, _len), do: Interpretation.at(witness, i, c)

  # Clamped so the row has a value; the pin then fails for that column, as it should.
  defp held({:aimed, address}, witness, x, len),
    do: address |> Semantics.column(witness, x) |> max(1) |> min(len)

  @spec pins([Ast.pred()], %{pos_integer() => Ast.address()}) :: [Ast.pred()]
  defp pins(parts, aimed) do
    for part <- parts,
        not match?({tag, _preds} when tag in [:conj, :disj], part),
        {_i, {:at, {:cell, row}, _mul, _add}} <- reads(part),
        is_map_key(aimed, row),
        uniq: true,
        do: Ast.eq(Ast.cell(row), Ast.naming(aimed[row]))
  end

  # A branch reading b columns back is undefined at x <= b, where the backend would read
  # the padding, so it holds only where `past/2` says that column is in the trace.
  @spec guarded(Ast.pred(), pos_integer()) :: Ast.pred()
  defp guarded(pred, len) do
    pred
    |> Ast.postwalk(fn
      {:disj, branches} -> {:disj, Enum.map(branches, &guard(&1, len))}
      node -> node
    end)
    |> guard(len)
  end

  @spec guard(Ast.pred(), pos_integer()) :: Ast.pred()
  defp guard(branch, len) do
    b = back(branch)

    if b < least(branch),
      do: branch,
      else: Ast.conj(Ast.conjuncts(branch) ++ [Ast.eq(past(b, len), 1)])
  end

  # The least column a branch's own conjuncts let it hold at.
  @spec least(Ast.pred()) :: pos_integer()
  defp least(branch) do
    branch
    |> Ast.conjuncts()
    |> Enum.map(fn
      {:natural, {:add, :x, k}} -> -k
      {:eq, :x, c} when is_integer(c) -> c
      _other -> 1
    end)
    |> Enum.max()
  end

  # A disjunction's branches guard their own reads, unless it sits in a term, where its
  # value counts and not only whether it holds.
  @spec back(Ast.pred() | Ast.term_t()) :: non_neg_integer()
  defp back({:disj, _branches}), do: 0
  defp back({:reify, phi}), do: Ast.reduce(phi, 0, &max(behind(&1), &2))
  defp back(node), do: Enum.reduce(Ast.children(node), behind(node), &max(back(&1), &2))

  @spec behind(Ast.pred() | Ast.term_t()) :: non_neg_integer()
  defp behind({:cell, _i, {:at, :x, 1, add}}) when add < 0, do: -add
  defp behind(_node), do: 0

  # Lookups and pointers range over private columns only, so a claimed row they touch
  # hands its claim to a copy.
  @spec twinned(Ast.pred(), Interpretation.t(), [pos_integer()], [pos_integer()]) ::
          {Ast.pred(), Interpretation.t(), [pos_integer()]}
  defp twinned(pred, witness, public, touched) do
    claimed = Enum.filter(public, &(&1 in touched))
    {witness, twins} = rowed(witness, claimed, &Interpretation.at(witness, &1, &2))
    bonds = for {i, twin} <- twins, do: Ast.eq(Ast.cell(twin), Ast.cell(i))

    pred =
      if bonds == [],
        do: pred,
        else:
          pred |> Ast.branches() |> Enum.map(&Ast.conj(Ast.conjuncts(&1) ++ bonds)) |> Ast.disj()

    {pred, witness, Enum.map(public, &Map.get(twins, &1, &1))}
  end

  @spec kind(Ast.read(), pos_integer()) :: kind()
  defp kind({_i, {:at, :x, 1, add}}, _len) when add <= 0, do: {:shift, -add}
  defp kind({_i, {:at, {:cell, _j}, 1, 0}}, _len), do: :pointer
  defp kind({i, {:at, _base, 0, c}}, len) when c in 1..len//1, do: {:tie, {i, c}}
  defp kind({_i, address}, _len), do: {:aimed, address}

  @spec nodes(Ast.pred() | Ast.term_t()) :: [Ast.pred() | Ast.term_t()]
  defp nodes(node) do
    node
    |> Ast.reduce([], &[&1 | &2])
    |> Enum.reverse()
  end

  @spec reads(Ast.pred() | Ast.term_t()) :: [Ast.read()]
  defp reads(node) do
    node
    |> nodes()
    |> Enum.map(&Ast.read/1)
    |> Enum.reject(&is_nil/1)
  end

  @spec obligations(Ast.pred()) :: [Ast.pred()]
  defp obligations(pred) do
    pred
    |> nodes()
    |> Enum.filter(&obligation?/1)
    |> Enum.uniq()
  end

  @spec obligation?(Ast.pred()) :: boolean()
  defp obligation?({tag, _t}) when tag in [:natural, :distinct], do: true
  defp obligation?({tag, _cells, _values}) when tag in [:permutes, :permuted], do: true
  defp obligation?(_pred), do: false

  # Obligations are proved by lookups, not by the polynomial.
  @spec stripped(Ast.pred()) :: Ast.pred()
  defp stripped(pred) do
    Ast.postwalk(pred, fn
      {:conj, parts} -> {:conj, Enum.reject(parts, &obligation?/1)}
      node -> node
    end)
  end

  # After `bounded_expressions/2` every natural is over a cell.
  @spec naturals([Ast.pred()]) :: [pos_integer()]
  defp naturals(obligations) do
    bounded = for {:natural, t} <- obligations, do: t
    bounded |> Enum.map(&elem(Ast.read(&1), 0)) |> Enum.uniq() |> Enum.sort()
  end

  @spec models(Ast.pred(), Interpretation.t()) :: :ok | {:error, Refusal.t()}
  defp models(pred, witness) do
    Refusal.refute(
      1..Interpretation.len(witness),
      &(not Semantics.holds?(pred, witness, &1)),
      &{:witness_unsatisfies_schedule, %{column: &1}}
    )
  end

  @spec claimed([Interpretation.claim()], Interpretation.t()) ::
          {:ok, [{String.t(), non_neg_integer()}]} | {:error, Refusal.t()}
  defp claimed(claims, witness) do
    Refusal.map(claims, fn {name, row, x} ->
      case Interpretation.fetch(witness, row, x) do
        {:ok, value} -> {:ok, {name, value}}
        :error -> {:error, {:claim_outside_witness, %{claim: name, row: row, column: x}}}
      end
    end)
  end

  ############################################################
  #                        The lookups                       #
  ############################################################

  @spec tables([Ast.pred()], pos_integer()) ::
          {:ok, [{[integer()], [[cell()]]}]} | {:error, Refusal.t()}
  defp tables(obligations, len) do
    tables = for {:permutes, cells, values} <- obligations, do: {values, cells}

    Refusal.map(tables, fn {values, cells} ->
      with {:ok, selections} <- Refusal.map(1..len, &standing(cells, &1, len)),
           do: {:ok, {values, Enum.uniq(selections)}}
    end)
  end

  @spec pairs([Ast.pred()], pos_integer()) :: {:ok, [[cell()]]} | {:error, Refusal.t()}
  defp pairs(obligations, len) do
    copies = for {:permuted, cells, copy} <- obligations, do: {cells, copy}

    Refusal.flat_map(copies, fn {cells, copy} ->
      Refusal.flat_map(1..len, fn x ->
        with {:ok, first} <- standing(cells, x, len),
             {:ok, second} <- standing(copy, x, len),
             do: {:ok, [first, second]}
      end)
    end)
  end

  # The backend takes a selection as fixed cells, so the address must not depend on the
  # witness and must lie in the trace.
  @spec standing([Ast.term_t()], pos_integer(), pos_integer()) ::
          {:ok, [cell()]} | {:error, Refusal.t()}
  defp standing(cells, x, len) do
    Refusal.map(cells, fn cell ->
      case Ast.read(cell) do
        {i, {:at, :x, mul, add}} when (mul * x + add) in 1..len//1 -> {:ok, {i, mul * x + add}}
        _elsewhere -> {:error, {:selection_outside_trace, %{cell: cell, column: x}}}
      end
    end)
  end

  # The backend checks a selection at every column, inactive branches included, so the
  # cells of an inactive selection are overwritten with the table. A claimed cell may not be.
  @spec filled(Interpretation.t(), [{[integer()], [[cell()]]}], [Interpretation.claim()]) ::
          {:ok, Interpretation.t()} | {:error, Refusal.t()}
  defp filled(witness, tables, claims) do
    held = fn {i, c} -> Interpretation.at(witness, i, c) end

    fills =
      for {values, selections} <- tables,
          cells <- selections,
          Enum.sort(Enum.map(cells, held)) != Enum.sort(values),
          {cell, value} <- Enum.zip(cells, values),
          into: %{},
          do: {cell, value}

    changed = fn {_name, i, c} -> Map.get(fills, {i, c}, held.({i, c})) != held.({i, c}) end

    with :ok <-
           Refusal.refute(claims, changed, fn {name, i, c} ->
             {:selection_changes_claim, %{claim: name, row: i, column: c}}
           end) do
      {:ok,
       Enum.reduce(fills, witness, fn {{i, c}, value}, w -> Interpretation.put(w, i, c, value) end)}
    end
  end

  # One lookup per table, so tables with the same values merge.
  @spec selected([{[integer()], [[cell()]]}], %{row() => non_neg_integer()}, pos_integer()) ::
          [ZincPlus.Selected.t()]
  defp selected(tables, cols, len) do
    for {values, selections} <- Enum.group_by(tables, &elem(&1, 0), &elem(&1, 1)) do
      {columns, selections} = slotted(Enum.concat(selections), cols, len)
      %ZincPlus.Selected{columns: columns, values: values, selections: selections}
    end
  end

  @spec permuted([[cell()]], %{row() => non_neg_integer()}, pos_integer()) ::
          [ZincPlus.Permuted.t()]
  defp permuted([], _cols, _len), do: []

  defp permuted(pairs, cols, len) do
    {columns, selections} = slotted(pairs, cols, len)
    pairs = selections |> Enum.chunk_every(2) |> Enum.map(&List.to_tuple/1)
    [%ZincPlus.Permuted{columns: columns, pairs: pairs}]
  end

  # The backend addresses a column by its position in the lookup's sorted column list,
  # and a trace column c as `len - c`.
  @spec slotted([[cell()]], %{row() => non_neg_integer()}, pos_integer()) ::
          {[non_neg_integer()], [[{non_neg_integer(), non_neg_integer()}]]}
  defp slotted(selections, cols, len) do
    columns = for {i, _c} <- Enum.concat(selections), uniq: true, do: cols[i]
    columns = Enum.sort(columns)
    slots = Map.new(Enum.with_index(columns))
    place = fn {i, c} -> {slots[cols[i]], len - c} end
    {columns, Enum.map(selections, &Enum.map(&1, place))}
  end

  ############################################################
  #                        The program                       #
  ############################################################

  # The backend has no column index, so X is a committed column, and the pins are what
  # keep it equal to the index and `ones` equal to 1.
  @spec polynomial(Ast.pred(), pos_integer()) :: Ast.ep()
  defp polynomial(pred, len) do
    poly =
      pred
      |> Ast.arithmetize()
      |> Ast.postwalk(fn
        :x -> Ast.cell(:x)
        :len -> len
        node -> node
      end)

    if Enum.any?([:x, :ones], &(&1 in Ast.reads(poly))),
      do: Ast.add(poly, Ast.arithmetize(pinned(len))),
      else: poly
  end

  # With one column the region is empty, so X is pinned to 1 directly.
  @spec pinned(pos_integer()) :: Ast.pred()
  defp pinned(1), do: Ast.eq(Ast.cell(:x), 1)

  # Where the column before is in the trace X steps by one; elsewhere X is 1.
  defp pinned(len) do
    x = Ast.cell(:x)
    ones = Ast.cell(:ones)
    region = past(1, len)
    stepped = Ast.sub(Ast.sub(x, Ast.at(:x, :x, 1, -1)), 1)

    Ast.conj([
      Ast.eq(ones, 1),
      Ast.eq(ones, Ast.at(:ones, :x, 1, -1)),
      Ast.eq(Ast.mul(region, stepped), 0),
      Ast.eq(Ast.mul(Ast.sub(1, region), Ast.sub(x, 1)), 0)
    ])
  end

  # `ones` is 1 throughout the cube and reads zero past its end, so read far enough back it
  # is 1 exactly where column x - b is in the trace. Past a trace of b columns, it is nowhere.
  @spec past(pos_integer(), pos_integer()) :: Ast.term_t()
  defp past(b, len) when b >= len, do: 0
  defp past(b, len), do: Ast.at(:ones, :x, 1, len - b - (1 <<< num_vars(len)))

  # Claimed rows first, then every row read or named, sorted, then X and ones.
  @spec layout(Ast.ep(), [pos_integer()], [pos_integer()]) :: [row()]
  defp layout(poly, public, unread) do
    reached = Enum.uniq(Enum.map(reads(poly), &elem(&1, 0)) ++ unread)
    witness_rows = reached |> Enum.filter(&is_integer/1) |> Enum.sort()
    public ++ (witness_rows -- public) ++ Enum.filter([:x, :ones], &(&1 in reached))
  end

  # After the passes every read of the polynomial is a column at a shift back.
  @spec shifts(Ast.ep(), %{row() => non_neg_integer()}) :: [shift()]
  defp shifts(poly, cols) do
    poly
    |> reads()
    |> Enum.map(fn {i, {:at, :x, 1, add}} -> {cols[i], -add} end)
    |> Enum.reject(fn {_col, back} -> back == 0 end)
    |> Enum.uniq()
    |> Enum.sort()
  end

  # Bottom up: by the time a node is reached its children are already their ops, so a
  # node's ops are those lists followed by its own op.
  @spec ops(Ast.ep(), %{row() => non_neg_integer()}, [shift()]) :: [op()]
  defp ops(poly, cols, shifts) do
    Ast.postwalk(poly, fn
      k when is_integer(k) ->
        [{:const, k}]

      {:cell, i} ->
        [{:up, cols[i]}]

      {:cell, i, {:at, :x, 1, add}} ->
        [{:down, Enum.find_index(shifts, &(&1 == {cols[i], -add}))}]

      {:add, left, right} ->
        left ++ right ++ [:add]

      {:mul, left, right} ->
        left ++ right ++ [:mul]
    end)
  end

  # A column lists x from `len` down to 1; the padding repeats column 1 so a base branch
  # holds there.
  @spec columns(Interpretation.t(), [row()]) :: [[integer()]]
  defp columns(witness, rows) do
    len = Interpretation.len(witness)
    padding = (1 <<< num_vars(len)) - len

    Enum.map(rows, fn row ->
      values = Enum.map(len..1//-1, &value(witness, row, &1))
      values ++ List.duplicate(List.last(values), padding)
    end)
  end

  @spec value(Interpretation.t(), row(), pos_integer()) :: integer()
  defp value(_witness, :x, x), do: x
  defp value(_witness, :ones, _x), do: 1
  defp value(witness, i, x), do: Interpretation.at(witness, i, x)
end
