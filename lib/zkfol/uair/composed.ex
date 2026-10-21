defmodule Zkfol.Uair.Composed do
  @moduledoc """
  I am Section 4's lowering and the mode it leaves behind.
  """

  use TypedStruct

  import Bitwise

  alias Zkfol.Ast
  alias Zkfol.Interpretation
  alias Zkfol.Refusal
  alias Zkfol.Uair
  alias Zkfol.Uair.Plain

  @typep row ::
           {:bit, pos_integer(), non_neg_integer()}
           | {:lower, pos_integer()}
           | {pos_integer(), pos_integer()}

  typedstruct enforce: true do
    field(:reads, [Uair.read()], default: [])
  end

  typedstruct module: Lowering do
    @typedoc """
    The composed reads in witness coordinates and the rows requiring Word bounds.
    """
    field(:reads, [Uair.read()], default: [])
    # Bound pointers even at the backend's exempt final row, and their pointer - 1 slacks.
    field(:bounded, [pos_integer()], default: [])
  end

  @doc "I lower every pointer read: mu bit rows apiece, a result row per deref, on the witness."
  @spec lower(Ast.pred(), Interpretation.t(), pos_integer()) ::
          {:ok, Ast.pred(), Interpretation.t(), Lowering.t()} | {:error, Refusal.t()}
  def lower(pred, witness, mu) do
    case Ast.pointer_derefs(pred) do
      [] ->
        {:ok, pred, witness, %Lowering{}}

      pairs ->
        # The order is load-bearing: asking whether a row is confined reads it.
        with :ok <- inside(pairs, witness),
             :ok <- confined(pairs, witness) do
          dynamic = pairs |> Enum.map(&elem(&1, 1)) |> Enum.uniq() |> Enum.sort()

          leaves =
            for(a <- dynamic, nu <- 0..(mu - 1), do: {:bit, a, nu}) ++
              Enum.map(dynamic, &{:lower, &1}) ++ pairs

          {witness, rows} = Uair.rowed(witness, leaves, &value(&1, witness, &2))

          bits =
            Map.new(dynamic, fn a -> {a, for(nu <- 0..(mu - 1), do: rows[{:bit, a, nu}])} end)

          reads =
            for {i, a} <- pairs do
              %{row: a, value_row: i, bit_rows: bits[a], result_row: rows[{i, a}]}
            end

          bounded = dynamic ++ Enum.map(dynamic, &rows[{:lower, &1}])

          {:ok, rewrite(pred, constraints(dynamic, bits, rows), rows), witness,
           %Lowering{reads: reads, bounded: bounded}}
        end
    end
  end

  @doc "I am the mode a lowering leaves: its rows in committed-column coordinates."
  @spec emitted(Lowering.t(), %{pos_integer() => non_neg_integer()}) :: Uair.mode()
  def emitted(%Lowering{reads: []}, _cols), do: %Plain{}

  def emitted(lowering, cols) do
    reads =
      for read <- lowering.reads do
        %{
          row: Map.fetch!(cols, read.row),
          value_row: Map.fetch!(cols, read.value_row),
          bit_rows: Enum.map(read.bit_rows, &Map.fetch!(cols, &1)),
          result_row: Map.fetch!(cols, read.result_row)
        }
      end

    %__MODULE__{reads: reads}
  end

  @spec spelled([pos_integer()], Ast.term_t()) :: [Ast.pred()]
  defp spelled(rows, source) do
    booleanity = for b <- rows, do: Ast.eq(Ast.mul(Ast.cell(b), Ast.cell(b)), Ast.cell(b))

    weighted =
      rows
      |> Enum.with_index()
      |> Enum.map(fn {b, nu} -> Ast.mul(Ast.cell(b), 1 <<< nu) end)

    booleanity ++ [Ast.eq(source, Enum.reduce(weighted, &Ast.add(&2, &1)))]
  end

  @spec inside([{pos_integer(), pos_integer()}], Interpretation.t()) ::
          :ok | {:error, Refusal.t()}
  defp inside(pairs, witness) do
    Refusal.refute(
      pairs |> Enum.flat_map(&Tuple.to_list/1) |> Enum.uniq(),
      &(&1 > Interpretation.arity(witness)),
      &{:read_row_outside_witness, %{row: &1}}
    )
  end

  # Definition 3.1(2): a dynamic pointer holds column indices.
  @spec confined([{pos_integer(), pos_integer()}], Interpretation.t()) ::
          :ok | {:error, Refusal.t()}
  defp confined(pairs, witness) do
    Refusal.refute(
      pairs |> Enum.map(&elem(&1, 1)) |> Enum.uniq(),
      fn a ->
        len = Interpretation.len(witness)
        witness |> Interpretation.rows() |> Enum.at(a - 1) |> Enum.any?(&(&1 not in 1..len))
      end,
      &{:pointer_row_outside_matrix, %{row: &1}}
    )
  end

  @spec constraints([pos_integer()], %{pos_integer() => [pos_integer()]}, %{
          row() => pos_integer()
        }) ::
          [Ast.pred()]
  defp constraints(dynamic, bits, rows) do
    Enum.flat_map(dynamic, fn a ->
      cube_index = Ast.add(Ast.len(), Ast.mul(Ast.cell(a), -1))

      spelled(Map.fetch!(bits, a), cube_index) ++
        [Ast.eq(Ast.cell(rows[{:lower, a}]), Ast.add(Ast.cell(a), -1))]
    end)
  end

  @spec rewrite(Ast.pred(), [Ast.pred()], %{row() => pos_integer()}) ::
          Ast.pred()
  defp rewrite(pred, constraints, results) do
    pred
    |> Ast.branches()
    |> Enum.map(fn branch ->
      parts =
        branch
        |> Ast.postwalk(fn node ->
          case Ast.read(node) do
            {i, {:at, {:cell, j}, 1, 0}} when is_map_key(results, {i, j}) ->
              Ast.cell(results[{i, j}])

            _other ->
              node
          end
        end)
        |> Ast.conjuncts()

      Ast.conj(parts ++ constraints)
    end)
    |> Ast.disj()
  end

  @spec value(row(), Interpretation.t(), pos_integer()) :: integer()
  defp value({:bit, a, nu}, witness, x),
    do: (Interpretation.len(witness) - Interpretation.at(witness, a, x)) |> bsr(nu) |> band(1)

  defp value({:lower, a}, witness, x), do: Interpretation.at(witness, a, x) - 1

  defp value({i, a}, witness, x),
    do: Interpretation.at(witness, i, Interpretation.at(witness, a, x))
end
