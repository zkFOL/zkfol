defmodule Zkfol.Lileum do
  @moduledoc "I am the Lileum backend"

  @behaviour Zkfol.Backend

  use TypedStruct

  alias Zkfol.Ast
  alias Zkfol.Interpretation
  alias Zkfol.Lileum.FourSquares
  alias Zkfol.Lileum.Native
  alias Zkfol.Refusal
  alias Zkfol.Semantics

  @typedoc "The upstream expression algebra"
  @type expression ::
          {:var, non_neg_integer()}
          | {:const, integer()}
          | {:add, expression(), expression()}
          | {:sub, expression(), expression()}
          | {:mul, expression(), expression()}
  @type cell :: {non_neg_integer(), non_neg_integer()}
  @type connection :: {cell(), cell()}

  typedstruct module: Structure, enforce: true do
    field(:rows, pos_integer())
    field(:columns, pos_integer())
    field(:arithmetic_constraints, [Zkfol.Lileum.expression()])
    field(:copy_constraints, [Zkfol.Lileum.connection()])
    field(:reads, [Zkfol.Lileum.connection()])
  end

  typedstruct enforce: true do
    field(:structure, Structure.t())
    field(:columns, [[integer()]])
  end

  typedstruct module: Translation do
    field(:value, Ast.ep(), enforce: true)
    field(:rows, [[integer()]], enforce: true)
    field(:constraints, [Ast.arithmetized()], default: [])
    field(:copies, [Zkfol.Lileum.connection()], default: [])
    field(:reads, [Zkfol.Lileum.connection()], default: [])
  end

  @impl true
  @spec prove(Ast.pred(), Interpretation.t(), keyword()) :: {:error, Refusal.t()}
  def prove(pred, witness, opts) do
    with {:ok, emitted} <- emit(pred, witness) do
      Native.prove(emitted.structure, emitted.columns, opts)
    end
  end

  @doc "I expand the source forms and encode their arithmetic and native reads."
  @spec emit(Ast.pred(), Interpretation.t()) :: {:ok, t()} | {:error, Refusal.t()}
  def emit(pred, witness) do
    arity = Interpretation.arity(witness)
    len = Interpretation.len(witness)
    refusal = &{:unliftable_term, %{term: &1}}

    with :ok <- Refusal.refute(Ast.to_list(pred), &unliftable?(&1, arity), refusal) do
      polynomial = Ast.arithmetize(pred)
      {translations, height} = translations(polynomial, witness)

      replacements =
        Map.new(translations, fn {node, translation} -> {node, translation.value} end)

      replacements = Map.put(replacements, :len, len)
      translated = Enum.map(translations, &elem(&1, 1))
      constraints = [polynomial | Enum.flat_map(translated, & &1.constraints)]

      structure = %Structure{
        rows: height,
        columns: len,
        arithmetic_constraints: Enum.map(constraints, &expression(&1, replacements)),
        copy_constraints: translated |> Enum.flat_map(& &1.copies) |> Enum.map(&connection/1),
        reads: translated |> Enum.flat_map(& &1.reads) |> Enum.map(&connection/1)
      }

      rows = Interpretation.rows(witness) ++ Enum.flat_map(translated, & &1.rows)
      {:ok, %__MODULE__{structure: structure, columns: Enum.zip_with(rows, & &1)}}
    end
  end

  @spec unliftable?(Ast.t(), pos_integer()) :: boolean()
  defp unliftable?({tag, _cells, _other}, _arity) when tag in [:permutes, :permuted], do: true
  defp unliftable?({:distinct, _cells}, _arity), do: true

  defp unliftable?(node, arity) do
    case Ast.read(node) do
      {i, {:at, {:cell, j}, _, _}} -> i not in 1..arity or j not in 1..arity
      {i, _address} -> i not in 1..arity
      nil -> false
    end
  end

  @spec translations(Ast.arithmetized(), Interpretation.t()) ::
          {[{Ast.arithmetized(), Translation.t()}], pos_integer()}
  defp translations(polynomial, witness) do
    reads = polynomial |> Ast.to_list() |> Enum.filter(&match?({:cell, _, _}, &1)) |> Enum.uniq()

    addresses =
      Enum.map(reads, fn read ->
        {_, address} = Ast.read(read)
        Ast.naming(address)
      end)

    forms =
      [polynomial | addresses]
      |> Enum.flat_map(&Ast.to_list/1)
      |> Enum.uniq()
      |> Enum.filter(&(&1 == :x or match?({:natural, _}, &1)))

    {expanded, next} =
      Enum.map_reduce(forms, Interpretation.arity(witness) + 1, fn node, first ->
        translation = expand(node, first, witness)
        {{node, translation}, first + length(translation.rows)}
      end)

    {read_rows, next} =
      Enum.map_reduce(reads, next, fn node, first -> {{node, {first, first + 1}}, first + 2} end)

    translated_reads =
      Enum.map(read_rows, fn {node, cells} -> {node, read(node, cells, next - 1, witness)} end)

    {expanded ++ translated_reads, next - 1}
  end

  # X is 1 at the first column, and each next column copies x + 1.
  @spec expand(Ast.arithmetized(), pos_integer(), Interpretation.t()) :: Translation.t()
  defp expand(:x, first, witness) do
    [x, next, one] = Enum.to_list(first..(first + 2))
    len = Interpretation.len(witness)
    chain = for c <- 2..len//1, do: {{next, c - 1}, {x, c}}

    %Translation{
      value: Ast.cell(x),
      rows: [Enum.to_list(1..len), Enum.to_list(2..(len + 1)), List.duplicate(1, len)],
      constraints: [Ast.sub(Ast.cell(next), Ast.add(Ast.cell(x), 1)), Ast.sub(Ast.cell(one), 1)],
      copies: [{{one, 1}, {x, 1}} | chain]
    }
  end

  # temporary expand around natruals with double squares
  defp expand({:natural, term}, first, witness) do
    [sign | roots] = Enum.map(first..(first + 4), &Ast.cell/1)
    magnitude = Ast.sub(Ast.mul(Ast.sub(1, Ast.mul(2, sign)), term), sign)

    columns =
      for c <- 1..Interpretation.len(witness) do
        v = Semantics.eval(term, witness, c)
        s = if v < 0, do: 1, else: 0
        [s | FourSquares.decompose((1 - 2 * s) * v - s)]
      end

    %Translation{
      value: sign,
      rows: Enum.zip_with(columns, & &1),
      constraints: [
        Ast.mul(sign, Ast.sub(sign, 1)),
        Ast.sub(magnitude, roots |> Enum.map(&Ast.mul(&1, &1)) |> Enum.reduce(&Ast.add/2))
      ]
    }
  end

  @spec read(Ast.ep_leaf(), {pos_integer(), pos_integer()}, pos_integer(), Interpretation.t()) ::
          Translation.t()
  defp read(node, {seen, pointer}, height, witness) do
    {i, address} = Ast.read(node)
    len = Interpretation.len(witness)
    flattened = Ast.add(Ast.mul(height, Ast.sub(Ast.naming(address), 1)), i - 1)

    columns =
      for c <- 1..len do
        column = Semantics.column(address, witness, c)
        [Interpretation.at(witness, i, column), height * (column - 1) + i - 1]
      end

    %Translation{
      value: Ast.cell(seen),
      rows: Enum.zip_with(columns, & &1),
      constraints: [Ast.sub(Ast.cell(pointer), flattened)],
      reads: for(c <- 1..len, do: {{pointer, c}, {seen, c}})
    }
  end

  @spec connection(connection()) :: connection()
  defp connection({{r, c}, {s, d}}), do: {{r - 1, c - 1}, {s - 1, d - 1}}

  @spec expression(Ast.arithmetized(), %{Ast.arithmetized() => Ast.ep()}) :: expression()
  defp expression(node, replacements) when is_map_key(replacements, node) do
    expression(Map.fetch!(replacements, node), replacements)
  end

  defp expression(q, _) when is_integer(q) do
    {:const, q}
  end

  defp expression({:cell, row}, _) do
    {:var, row - 1}
  end

  defp expression({:add, a, {:mul, b, -1}}, replacements) do
    {:sub, expression(a, replacements), expression(b, replacements)}
  end

  defp expression({:add, a, b}, replacements) do
    {:add, expression(a, replacements), expression(b, replacements)}
  end

  defp expression({:mul, a, b}, replacements) do
    {:mul, expression(a, replacements), expression(b, replacements)}
  end
end
