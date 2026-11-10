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

  @type named :: {Ast.arithmetized(), pos_integer()}

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
    field(:cells, [[integer()]], enforce: true)
    field(:constraints, [Ast.arithmetized()], default: [])
    field(:copies, [{Zkfol.Lileum.named(), Zkfol.Lileum.named()}], default: [])
    field(:reads, [{Zkfol.Lileum.named(), Zkfol.Lileum.named()}], default: [])
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
    len = Interpretation.len(witness)
    refusal = &{:unliftable_term, %{term: &1}}

    with :ok <- Refusal.refute(Ast.to_list(pred), &unliftable?/1, refusal) do
      polynomial = pred |> Ast.arithmetize() |> Ast.postwalk(&if(&1 == :len, do: len, else: &1))
      forms = polynomial |> Ast.to_list() |> Enum.filter(&(rows(&1) != [])) |> Enum.uniq()
      source = Enum.map(1..Interpretation.arity(witness), &Ast.cell/1)
      vars = (source ++ Enum.flat_map(forms, &rows/1)) |> Enum.with_index() |> Map.new()
      height = map_size(vars)
      translated = Enum.map(forms, &expand(&1, height, witness))
      constraints = [polynomial | Enum.flat_map(translated, & &1.constraints)]
      connection = fn {{a, c}, {b, d}} -> {{vars[a], c - 1}, {vars[b], d - 1}} end

      structure = %Structure{
        rows: height,
        columns: len,
        arithmetic_constraints: Enum.map(constraints, &expression(&1, vars)),
        copy_constraints: translated |> Enum.flat_map(& &1.copies) |> Enum.map(connection),
        reads: translated |> Enum.flat_map(& &1.reads) |> Enum.map(connection)
      }

      rows = Interpretation.rows(witness) ++ Enum.flat_map(translated, & &1.cells)
      {:ok, %__MODULE__{structure: structure, columns: Enum.zip_with(rows, & &1)}}
    end
  end

  @spec unliftable?(Ast.t()) :: boolean()
  defp unliftable?({tag, _cells, _other}) when tag in [:permutes, :permuted], do: true
  defp unliftable?({:distinct, _cells}), do: true
  defp unliftable?(_node), do: false

  @spec rows(Ast.arithmetized()) :: [Ast.arithmetized()]
  defp rows(:x), do: [:x, Ast.cell(:next), Ast.cell(:one)]
  defp rows({:natural, _} = sign), do: [sign | Enum.map(1..4, &Ast.cell({:root, {sign, &1}}))]
  defp rows({:cell, _, {:at, :x, _, _}} = read), do: [read]
  defp rows({:cell, _, _} = read), do: [read, Ast.cell({:pointer, read})]
  defp rows(_node), do: []

  # X is 1 at the first column, and each next column copies x + 1.
  @spec expand(Ast.arithmetized(), pos_integer(), Interpretation.t()) :: Translation.t()
  defp expand(:x, _height, witness) do
    [x, next, one] = rows(:x)
    chain = for c <- 2..Interpretation.len(witness)//1, do: {{next, c - 1}, {x, c}}

    %Translation{
      cells: Enum.map([x, Ast.add(x, 1), 1], &values(&1, witness)),
      constraints: [Ast.sub(next, Ast.add(x, 1)), Ast.sub(one, 1)],
      copies: [{{one, 1}, {x, 1}} | chain]
    }
  end

  # temporary expand around natruals with double squares
  defp expand({:natural, term} = sign, _height, witness) do
    [_sign | roots] = rows(sign)
    magnitude = Ast.sub(Ast.mul(Ast.sub(1, Ast.mul(2, sign)), term), sign)
    squares = magnitude |> values(witness) |> Enum.map(&FourSquares.decompose/1)

    %Translation{
      cells: [values(sign, witness) | Enum.zip_with(squares, & &1)],
      constraints: [
        Ast.mul(sign, Ast.sub(sign, 1)),
        Ast.sub(magnitude, roots |> Enum.map(&Ast.mul(&1, &1)) |> Enum.reduce(&Ast.add/2))
      ]
    }
  end

  defp expand({:cell, i, {:at, :x, _, _} = address} = read, _height, witness) do
    len = Interpretation.len(witness)

    %Translation{
      cells: [values(read, witness)],
      copies: for(c <- 1..len, do: {{Ast.cell(i), Ast.column(address, c)}, {read, c}})
    }
  end

  defp expand({:cell, _, _} = read, height, witness) do
    {i, address} = Ast.read(read)
    [_read, pointer] = rows(read)
    flattened = Ast.add(Ast.mul(height, Ast.sub(Ast.naming(address), 1)), i - 1)

    %Translation{
      cells: [values(read, witness), values(flattened, witness)],
      constraints: [Ast.sub(pointer, flattened)],
      reads: for(c <- 1..Interpretation.len(witness), do: {{pointer, c}, {read, c}})
    }
  end

  @spec values(Ast.arithmetized(), Interpretation.t()) :: [integer()]
  defp values(term, witness) do
    len = Interpretation.len(witness)
    read = &Interpretation.at(witness, &1, &2)
    Enum.map(1..len, &Semantics.eval(term, len, &1, read))
  end

  @spec expression(Ast.arithmetized(), %{Ast.arithmetized() => non_neg_integer()}) :: expression()
  defp expression(q, _) when is_integer(q) do
    {:const, q}
  end

  defp expression({:add, a, {:mul, b, -1}}, vars) do
    {:sub, expression(a, vars), expression(b, vars)}
  end

  defp expression({:add, a, b}, vars) do
    {:add, expression(a, vars), expression(b, vars)}
  end

  defp expression({:mul, a, b}, vars) do
    {:mul, expression(a, vars), expression(b, vars)}
  end

  defp expression(row, vars) do
    {:var, Map.fetch!(vars, row)}
  end
end
