defmodule Zkfol.Semantics do
  @moduledoc """
  I am the integer semantics of the logic: Figure 3 of the paper, where zero
  is the one true value and predicates never go negative (Lemma 2.17).
  """

  alias Zkfol.Ast
  alias Zkfol.Interpretation

  @type reader :: (Ast.row_ref(), integer() -> integer() | :error)

  @doc "I evaluate a term or predicate at column `x` under `itp`; for a predicate 0 is true."
  @spec eval(Ast.term_t() | Ast.pred(), Interpretation.t(), pos_integer()) :: integer() | :error
  def eval(node, itp, x),
    do: eval(node, Interpretation.len(itp), x, &fetch(itp, &1, &2))

  @doc "I evaluate against supplied cells, including cells derived on demand from expressions."
  @spec eval(Ast.term_t() | Ast.pred(), pos_integer(), pos_integer(), reader()) ::
          integer() | :error
  def eval(q, _len, _x, _read) when is_integer(q), do: q
  def eval(:x, _len, x, _read), do: x
  def eval(:len, len, _x, _read), do: len
  def eval({:cell, _i} = cell, _len, x, read), do: at(cell, read, x)
  def eval({:cell, _i, _address} = cell, _len, x, read), do: at(cell, read, x)
  def eval({:reify, phi}, len, x, read), do: eval(phi, len, x, read)
  def eval({:mul, a, b}, len, x, read), do: product([a, b], len, x, read, 1)
  def eval({:disj, phis}, len, x, read), do: product(phis, len, x, read, 1)

  def eval({:add, a, b}, len, x, read) do
    with [a, b] <- defined([a, b], len, x, read), do: a + b
  end

  def eval({:eq, a, b}, len, x, read) do
    with [a, b] <- defined([a, b], len, x, read), do: (a - b) * (a - b)
  end

  def eval({:natural, t}, len, x, read) do
    with [v] <- defined([t], len, x, read), do: if(v >= 0, do: 0, else: 1)
  end

  def eval({:conj, phis}, len, x, read) do
    with vs when is_list(vs) <- defined(phis, len, x, read), do: Enum.sum(vs)
  end

  def eval({:permutes, cells, values}, len, x, read) do
    with vs when is_list(vs) <- defined(cells, len, x, read),
         do: if(Enum.sort(vs) == Enum.sort(values), do: 0, else: 1)
  end

  def eval({:distinct, cells}, len, x, read) do
    with vs when is_list(vs) <- defined(cells, len, x, read),
         do: if(length(Enum.uniq(vs)) == length(vs), do: 0, else: 1)
  end

  def eval({:permuted, cells, copy}, len, x, read) do
    with vs when is_list(vs) <- defined(cells, len, x, read),
         ws when is_list(ws) <- defined(copy, len, x, read),
         do: if(Enum.sort(vs) == Enum.sort(ws), do: 0, else: 1)
  end

  @doc "I am the column an address names under `itp` at `x`, or `:error` off the matrix."
  @spec column(Ast.address(), Interpretation.t(), pos_integer()) :: integer() | :error
  def column(address, itp, x), do: addressed(address, &fetch(itp, &1, &2), x)

  @spec at(Ast.term_t(), reader(), pos_integer()) :: integer() | :error
  defp at(cell, read, x) do
    {i, address} = Ast.read(cell)
    with at when is_integer(at) <- addressed(address, read, x), do: read.(i, at)
  end

  @spec addressed(Ast.address(), reader(), pos_integer()) :: integer() | :error
  defp addressed({:at, base, _mul, _add} = address, read, x) do
    b = if base == :x, do: x, else: read.(elem(base, 1), x)
    with b when is_integer(b) <- b, do: Ast.column(address, b)
  end

  @spec fetch(Interpretation.t(), Ast.row_ref(), integer()) :: integer() | :error
  defp fetch(itp, i, x) do
    with {:ok, held} <- Interpretation.fetch(itp, i, x), do: held
  end

  # The values of `nodes` in order, or :error at the first one undefined.
  @spec defined([Ast.term_t() | Ast.pred()], pos_integer(), pos_integer(), reader()) ::
          [integer()] | :error
  defp defined([], _len, _x, _read), do: []

  defp defined([node | rest], len, x, read) do
    with v when is_integer(v) <- eval(node, len, x, read),
         vs when is_list(vs) <- defined(rest, len, x, read),
         do: [v | vs]
  end

  # A zero factor makes the product zero even beside an undefined cell.
  @spec product(
          [Ast.term_t() | Ast.pred()],
          pos_integer(),
          pos_integer(),
          reader(),
          integer() | :error
        ) ::
          integer() | :error
  defp product([], _len, _x, _read, acc), do: acc

  defp product([node | rest], len, x, read, acc) do
    case eval(node, len, x, read) do
      0 -> 0
      :error -> product(rest, len, x, read, :error)
      _v when acc == :error -> product(rest, len, x, read, :error)
      v -> product(rest, len, x, read, acc * v)
    end
  end

  @doc "I am the judgement: `itp` satisfies `phi` exactly when `phi` is 0 at every column."
  @spec valid?(Ast.pred(), Interpretation.t()) :: boolean()
  def valid?(phi, itp), do: Enum.all?(1..Interpretation.len(itp), &holds?(phi, itp, &1))

  @doc "I am true when `phi` holds at column `x` under `itp`; an undefined cell holds nothing."
  @spec holds?(Ast.pred(), Interpretation.t(), pos_integer()) :: boolean()
  def holds?(phi, itp, x), do: eval(phi, itp, x) == 0
end
