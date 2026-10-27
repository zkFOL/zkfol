defmodule Zkfol.Prims do
  @moduledoc """
  I am the library the surface's comparisons, reductions and reads call:
  each is a relation whose body is its meaning, written once.
  `mod(e, m, r)` keeps its quotient local; comparisons keep their slack local.
  """

  use Zkfol.Lang
  import Zkfol.FOL

  @phi {Zkfol.Ast, :natural}
  @al ">= X 0"
  defrel natural(x)

  @al "> A B"
  defrel gt(a, b) do
    a = b + 1 + s
    natural(s)
  end

  @al ">= A B"
  defrel gte(a, b) do
    a = b + s
    natural(s)
  end

  @al "< A B"
  defrel lt(a, b) do
    b = a + 1 + s
    natural(s)
  end

  @al "<= A B"
  defrel lte(a, b) do
    b = a + s
    natural(s)
  end

  @phi {Zkfol.Ast, :nth}
  defrel nth(1, [v | _], v)

  defrel nth(n, [_ | t], v) do
    n1 = n - 1
    nth(n1, t, v)
  end

  # One branch stands above, the other below: apart either way.
  defrel neq(a, b) do
    a = b + 1 + s
    natural(s)
  end

  defrel neq(a, b) do
    b = a + 1 + s
    natural(s)
  end

  # AL narrows a free grid by `all_dif`; pairwise slack has no bound and exhausts the heap.
  # The clauses define it for a list the lowering cannot read as cells: each element is
  # absent from the rest.
  @phi {Zkfol.Ast, :distinct}
  @al {:definition, "all_dif Cells"}
  defrel all_distinct(cells) do
    pairwise(cells)
  end

  defrel pairwise([])

  defrel pairwise([x | xs]) do
    absent(x, xs)
    pairwise(xs)
  end

  defrel absent(_x, [])

  defrel absent(x, [y | ys]) do
    neq(x, y)
    absent(x, ys)
  end

  # The values are the circuit's own: one prescribed lookup, no copy.
  @phi {Zkfol.Ast, :permutation}
  defrel permutation(n, cells) do
    length(cells, n)
    each(cells, between(1, n))
    all_distinct(cells)
  end

  # Evaluation only: a free cell takes each value of its domain in turn.
  @al "label X"
  defrel label(x)

  defrel mod(e, m, r) do
    e = m * q + r
    r < m
    natural(r)
    natural(q)
  end
end
