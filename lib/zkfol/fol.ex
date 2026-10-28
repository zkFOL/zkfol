defmodule Zkfol.FOL do
  @moduledoc """
  I represent the standard library for FOL.

  ### Public API

  - `array/0`: `array(dimensions, value)`, a rectangular array of scalar cells.
  - `each/0`: `each(xs, r)`, `r` holding of every cell.
  - `map/0`: `map(xs, r, ys)`, `ys` the image of `xs` under `r`.
  - `length/0`: `length(xs, n)`.
  - `between/0`: `between(lo, hi, x)`.
  - `append/0`: `append(xs, ys, zs)`.
  - `concat/0`: `concat(xss, zs)`, the sequences of `xss` one after another.
  - `chunk/0`: `chunk(n, xs, ys)`, `xs` in runs of `n`.
  - `split/0`: `split(n, xs, ys, zs)`, the first `n` cells of `xs` and the rest.
  - `column/0`: `column(rows, cols)`, `cols` the transpose of `rows`.
  - `heads/0`: `heads(rows, hs, ts)`, one cell off the front of every row.
  """

  use Zkfol.Lang

  @phi {Zkfol.Array, :array}
  defrel array(dimensions, x) do
    each(dimensions, Zkfol.Prims.natural())
    array_cells(dimensions, x)
  end

  defrel array_cells([], x) do
    x = x + 0
  end

  defrel array_cells([n | dimensions], xs) do
    length(xs, n)
    each(xs, array_cells(dimensions))
  end

  defrel each([], _r)

  defrel each([x | xs], r) do
    r(x)
    each(xs, r)
  end

  defrel map([], _r, [])

  defrel map([x | xs], r, [y | ys]) do
    r(x, y)
    map(xs, r, ys)
  end

  defrel length([], 0)

  defrel length([_ | xs], n) do
    length(xs, m)
    n = m + 1
  end

  @al {:definition, ">= X Lo, <= X Hi"}
  defrel between(lo, hi, x) do
    x >= lo
    x <= hi
  end

  defrel append([], ys, ys)

  defrel append([h | t], ys, [h | zs]) do
    append(t, ys, zs)
  end

  defrel concat([], [])

  defrel concat([xs | rest], zs) do
    concat(rest, ys)
    append(xs, ys, zs)
  end

  defrel chunk(_n, [], [])

  defrel chunk(n, [h | t], [c | cs]) do
    split(n, [h | t], c, rest)
    chunk(n, rest, cs)
  end

  defrel split(0, xs, [], xs)

  defrel split(n, [h | t], [h | p], rest) do
    n > 0
    split(n - 1, t, p, rest)
  end

  defrel heads([], [], [])

  defrel heads([[h | t] | rs], [h | hs], [t | ts]) do
    heads(rs, hs, ts)
  end

  defrel column([[] | _], [])

  defrel column([[h | t] | rows], [c | cs]) do
    heads([[h | t] | rows], c, rest)
    column(rest, cs)
  end
end
