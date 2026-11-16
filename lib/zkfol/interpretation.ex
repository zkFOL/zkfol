defmodule Zkfol.Interpretation do
  @moduledoc """
  I am an interpretation of the matrix symbol C, Definition 2.16 of the paper: one
  rectangular matrix of integers, `C@i,x` its row `i` column `x`, 1-based.
  """

  use TypedStruct

  @typedoc "I denote if a particular cell in the witness is made public.
            The layout is: {label, row, column}"
  @type claim :: {String.t(), pos_integer(), pos_integer()}

  typedstruct enforce: true do
    field(:rows, tuple())
  end

  @doc "I build an interpretation from equal-length rows of integers."
  @spec new([[integer()]]) :: t()
  def new([first | _] = rows) when first != [] do
    widths = rows |> Enum.map(&length/1) |> Enum.uniq()

    unless widths == [length(first)] do
      raise ArgumentError, "rows must have equal length, got #{inspect(widths)}"
    end

    for row <- rows, entry <- row, not is_integer(entry) do
      raise ArgumentError, "entries must be integers, got #{inspect(entry)}"
    end

    %__MODULE__{rows: rows |> Enum.map(&List.to_tuple/1) |> List.to_tuple()}
  end

  @doc "I am my rows as lists: the shape `new/1` accepts."
  @spec rows(t()) :: [[integer()]]
  def rows(%__MODULE__{rows: rows}),
    do: rows |> Tuple.to_list() |> Enum.map(&Tuple.to_list/1)

  @doc "I return C@i,x."
  @spec at(t(), pos_integer(), pos_integer()) :: integer()
  def at(%__MODULE__{rows: rows}, i, x), do: rows |> elem(i - 1) |> elem(x - 1)

  @doc "I return `{:ok, C@i,x}`, or `:error` when the cell lies outside me."
  @spec fetch(t(), pos_integer(), pos_integer()) :: {:ok, integer()} | :error
  def fetch(%__MODULE__{rows: rows}, i, x) when i in 1..tuple_size(rows)//1,
    do: cell(elem(rows, i - 1), x)

  def fetch(_itp, _i, _x), do: :error

  @spec cell(tuple(), integer()) :: {:ok, integer()} | :error
  defp cell(row, x) when x in 1..tuple_size(row)//1, do: {:ok, elem(row, x - 1)}
  defp cell(_row, _x), do: :error

  @doc "I am me with C@i,x replaced."
  @spec put(t(), pos_integer(), pos_integer(), integer()) :: t()
  def put(%__MODULE__{rows: rows}, i, x, value),
    do: %__MODULE__{rows: put_elem(rows, i - 1, put_elem(elem(rows, i - 1), x - 1, value))}

  @doc "I return the number of rows, ar(C)."
  @spec arity(t()) :: pos_integer()
  def arity(%__MODULE__{rows: rows}), do: tuple_size(rows)

  @doc "I return the number of columns, len(C)."
  @spec len(t()) :: pos_integer()
  def len(%__MODULE__{rows: rows}), do: rows |> elem(0) |> tuple_size()
end
