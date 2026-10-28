defmodule Zkfol.Ast do
  @moduledoc """
  I am the syntax of the logic: Figure 1 of the paper, as data.

      t   ::= q | t + t | t * t | len(C) | reify(phi) | X | C_i(X) | C_i(mX + a) | C_i(C_j(X))
      phi ::= t = t | phi and phi | phi or phi | natural(t)
      e   ::= q | e + e | e * e | len(C) | X | C_i(X) | C_i(mX + a) | C_i(C_j(X))
  """

  @type poly(leaf) ::
          leaf
          | integer()
          | {:add, poly(leaf), poly(leaf)}
          | {:mul, poly(leaf), poly(leaf)}

  @type row_ref :: pos_integer() | atom() | {atom(), term()}

  @typedoc "The current column or where the row is"
  @type address_base :: :x | {:cell, row_ref()}

  @typedoc "the column `mul * base + add`."
  @type address :: {:at, address_base(), integer(), integer()}

  @typedoc "The leaves Figure 2's polynomials"
  @type ep_leaf ::
          :x
          | :len
          | {:cell, row_ref()}
          | {:cell, row_ref(), row_ref()}
          | {:cell, row_ref(), address()}

  @typedoc "Figure 2's enriched polynomials: the reify-free subsyntax of terms."
  @type ep :: poly(ep_leaf())

  @typedoc "Figure 1's terms: `t:ep/0` plus reify, closed under + and ×."
  @type term_t :: poly(ep_leaf() | {:reify, pred()})

  @type pred(t) ::
          {:eq, t, t}
          | {:conj, [pred(t)]}
          | {:disj, [pred(t)]}
          | {:natural, t}
          | {:permutes, [t], [integer()]}
          | {:distinct, [t]}
          | {:permuted, [t], [t]}

  @type pred :: pred(term_t())

  @doc "I the current column."
  @spec x() :: term_t()
  def x, do: :x

  @doc "The number of columns"
  @spec len() :: term_t()
  def len, do: :len

  @doc "Row `i` at the current column"
  @spec cell(row_ref()) :: term_t()
  def cell(i), do: {:cell, i}

  @doc "Row `i` at the column stored in row `j` of the current column."
  @spec cell(row_ref(), row_ref()) :: term_t()
  def cell(i, j), do: {:cell, i, j}

  @doc "I am the address `m·b + a`, `b` the current column or the one a row holds."
  @spec address(address_base(), integer(), integer()) :: address()
  def address(base, mul, add), do: {:at, base, mul, add}

  @doc "Row `i` at the column the affine term names, `read/1`'s inverse."
  @spec at(row_ref(), address_base(), integer(), integer()) :: term_t()
  def at(i, :x, 1, 0), do: cell(i)
  def at(i, {:cell, j}, 1, 0), do: cell(i, j)
  def at(i, base, mul, add), do: {:cell, i, address(base, mul, add)}

  @typedoc "The row, and the address its column is."
  @type read :: {row_ref(), address()}

  @spec read(term_t()) :: read() | nil
  def read({:cell, i}), do: {i, {:at, :x, 1, 0}}
  def read({:cell, i, {:at, base, mul, add}}), do: {i, {:at, base, mul, add}}
  def read({:cell, i, j}), do: {i, {:at, {:cell, j}, 1, 0}}
  def read(_node), do: nil

  @doc "I am the column an address names: `m·b + a`."
  @spec naming(address()) :: ep()
  def naming({:at, :x, mul, add}), do: add(mul(x(), mul), add)
  def naming({:at, {:cell, j}, mul, add}), do: add(mul(cell(j), mul), add)

  @doc "I am the column an address names: `m·b + a`."
  @spec column(address(), integer()) :: integer()
  def column({:at, _base, mul, add}, base), do: mul * base + add

  @doc "I substitute a call's address for X in an address; nested pointer reads cannot be expressed."
  @spec reframe(address(), address()) :: address() | nil
  def reframe({:at, :x, m, a}, {:at, base, scale, offset}),
    do: address(base, m * scale, m * offset + a)

  def reframe(_address, _call), do: nil

  @doc "I recover an address in the callee's coordinates, when its scale divides exactly."
  @spec unframe(address() | nil, address()) :: address() | nil
  def unframe({:at, :x, 0, a}, {:at, :x, _scale, _offset}), do: address(:x, 0, a)

  def unframe({:at, :x, m, a}, {:at, :x, scale, offset})
      when scale != 0 and rem(m, scale) == 0,
      do: address(:x, div(m, scale), a - div(m, scale) * offset)

  def unframe(_address, _call), do: nil

  @doc "I am t + u, born canonical: constants fold and ride right, through a sum's own, zero vanishes."
  @spec add(poly(l), poly(l)) :: poly(l) when l: var
  def add(q, r) when is_integer(q) and is_integer(r), do: q + r
  def add(0, t), do: t
  def add(t, 0), do: t
  def add({:add, t, q}, r) when is_integer(q) and is_integer(r), do: add(t, q + r)
  def add(q, t) when is_integer(q), do: {:add, t, q}
  def add(t, u), do: {:add, t, u}

  @doc "I am t - u: `add/2` of the negation."
  @spec sub(poly(l), poly(l)) :: poly(l) when l: var
  def sub(t, u), do: add(t, mul(u, -1))

  @doc "I am t * u, born canonical: constants fold and ride right, zero and one vanish."
  @spec mul(poly(l), poly(l)) :: poly(l) when l: var
  def mul(q, r) when is_integer(q) and is_integer(r), do: q * r
  def mul(0, _t), do: 0
  def mul(_t, 0), do: 0
  def mul(1, t), do: t
  def mul(t, 1), do: t
  def mul(q, t) when is_integer(q), do: {:mul, t, q}
  def mul(t, u), do: {:mul, t, u}

  @doc "I am reify(phi): the truth value of `phi` as a term."
  @spec reify(pred()) :: term_t()
  def reify(phi), do: {:reify, phi}

  @doc "I am t = u, born canonical: a constant rides right, as in a sum."
  @spec eq(t, t) :: pred(t) when t: var
  def eq(q, u) when is_integer(q) and not is_integer(u), do: {:eq, u, q}
  def eq(t, u), do: {:eq, t, u}

  @doc "I am the conjunction of `preds`; the grammar has no empty conjunction."
  @spec conj([pred(), ...]) :: pred()
  def conj([_ | _] = preds), do: {:conj, preds}

  @doc "I am the disjunction of `preds`; the grammar has no empty disjunction."
  @spec disj([pred(), ...]) :: pred()
  def disj([_ | _] = preds), do: {:disj, preds}

  @doc "I am the read at a computed index: a disjunction over `cells`, a branch a cell."
  @spec nth(term_t(), [term_t()], term_t()) :: pred()
  def nth(_index, [], _value), do: eq(0, 1)

  def nth(q, cells, value) when is_integer(q) and is_list(cells),
    do: if(q in 1..length(cells)//1, do: eq(value, Enum.at(cells, q - 1)), else: eq(0, 1))

  def nth(index, cells, value) when is_list(cells),
    do:
      disj(for {cell, i} <- Enum.with_index(cells, 1), do: conj([eq(index, i), eq(value, cell)]))

  def nth(_index, cells, _value), do: throw({:refused, {:unliftable_term, %{term: cells}}})

  @doc "I am distinct(cells): the cells hold pairwise different values, no polynomial."
  @spec distinct([term_t()]) :: pred()
  def distinct(cells) when not is_list(cells),
    do: throw({:refused, {:unliftable_term, %{term: cells}}})

  def distinct(cells), do: {:distinct, cells}

  @doc "I am permutation(n, cells): the cells hold 1..n exactly, `permutes/2` over them."
  @spec permutation(term_t(), [term_t()]) :: pred()
  def permutation(n, cells) when is_integer(n) and is_list(cells) do
    if n == length(cells), do: permutes(cells, Enum.to_list(1..n//1)), else: eq(0, 1)
  end

  def permutation(_n, cells), do: throw({:refused, {:unliftable_term, %{term: cells}}})

  @doc "I am permuted(cells, copy): the two hold one multiset, whatever it is."
  @spec permuted([term_t()], [term_t()]) :: pred()
  def permuted(cells, copy), do: {:permuted, cells, copy}

  @doc "I am natural(t): a naturality obligation, discharged by lookup, never a polynomial."
  @spec natural(t) :: pred(t) when t: var
  def natural(t), do: {:natural, t}

  @doc "I am permutes(cells, values): the cells hold `values` as a multiset, no polynomial."
  @spec permutes([t], [integer()]) :: pred(t) when t: var
  def permutes(cells, values), do: {:permutes, cells, values}

  @doc """
  I am Figure 2's polynomial for `pred`; `Zkfol.Semantics` evaluates the same rules
  independently so the oracle catches a bad lowering.
  """
  @spec arithmetize(pred()) :: ep()
  def arithmetize(pred) do
    postwalk(pred, fn
      {:eq, t, u} ->
        difference = sub(t, u)
        mul(difference, difference)

      # A conjunction wholly discharged by obligations arithmetizes to zero.
      {:conj, preds} ->
        Enum.reduce(preds, 0, &add/2)

      {:disj, preds} ->
        Enum.reduce(preds, &mul/2)

      {:reify, t} ->
        t

      node ->
        node
    end)
  end

  @doc "I am the degree of `pred`'s Figure 2 polynomial."
  @spec degree(pred()) :: non_neg_integer()
  def degree(pred), do: pred |> arithmetize() |> poly_degree()

  # `len` is a constant at emit and a naturality a lookup, so neither has degree.
  @spec poly_degree(ep()) :: non_neg_integer()
  defp poly_degree({:add, t, u}), do: max(poly_degree(t), poly_degree(u))
  defp poly_degree({:mul, t, u}), do: poly_degree(t) + poly_degree(u)
  defp poly_degree(:x), do: 1
  defp poly_degree(t), do: if(read(t), do: 1, else: 0)

  @doc """
  I am the equations `pred` still owes: none where a constant decides it
  true, falsity where a constant decides it false, `pred` itself where
  nothing is decided.
  """
  @spec folded(pred(t)) :: [pred(t)] when t: var
  def folded({:natural, q}) when is_integer(q), do: if(q >= 0, do: [], else: [eq(0, 1)])

  def folded({:eq, a, b}) when is_integer(a) and is_integer(b),
    do: if(a == b, do: [], else: [eq(0, 1)])

  def folded(pred), do: [pred]

  @doc "I am the branches of `pred`: a disjunction's disjuncts, any other predicate alone."
  @spec branches(pred()) :: [pred()]
  def branches({:disj, preds}), do: preds
  def branches(pred), do: [pred]

  @doc "I am the conjuncts of `pred`: a conjunction's members flattened, any other alone."
  @spec conjuncts(pred()) :: [pred()]
  def conjuncts({:conj, preds}), do: Enum.flat_map(preds, &conjuncts/1)
  def conjuncts(pred), do: [pred]

  @spec map_children(node, (node -> node)) :: node when node: var
  defp map_children({:add, t, u}, fun), do: {:add, fun.(t), fun.(u)}
  defp map_children({:mul, t, u}, fun), do: {:mul, fun.(t), fun.(u)}
  defp map_children({:reify, phi}, fun), do: {:reify, fun.(phi)}
  defp map_children({:eq, t, u}, fun), do: {:eq, fun.(t), fun.(u)}
  defp map_children({:natural, t}, fun), do: {:natural, fun.(t)}

  defp map_children({:permutes, cells, values}, fun),
    do: {:permutes, Enum.map(cells, fun), values}

  defp map_children({:distinct, cells}, fun), do: {:distinct, Enum.map(cells, fun)}

  defp map_children({:permuted, cells, copy}, fun),
    do: {:permuted, Enum.map(cells, fun), Enum.map(copy, fun)}

  defp map_children({:conj, preds}, fun), do: {:conj, Enum.map(preds, fun)}
  defp map_children({:disj, preds}, fun), do: {:disj, Enum.map(preds, fun)}
  defp map_children(leaf, _fun), do: leaf

  @doc "I rewrite bottom-up: children first, then `fun` on the rebuilt node."
  @spec postwalk(node, (node -> node)) :: node when node: var
  def postwalk(node, fun), do: fun.(map_children(node, &postwalk(&1, fun)))

  @doc "I am the immediate children of `node`: its subterms and subpredicates, none for a leaf."
  @spec children(node) :: [node] when node: var
  def children({tag, t, u}) when tag in [:add, :mul, :eq], do: [t, u]
  def children({:reify, phi}), do: [phi]
  def children({:natural, t}), do: [t]
  def children({:permutes, cells, _values}), do: cells
  def children({:distinct, cells}), do: cells
  def children({:permuted, cells, copy}), do: cells ++ copy
  def children({tag, preds}) when tag in [:conj, :disj], do: preds
  def children(_leaf), do: []

  @doc "I fold `fun` over every node, each parent before its children (pre-order)."
  @spec reduce(node, acc, (node, acc -> acc)) :: acc when node: var, acc: var
  def reduce(node, acc, fun),
    do: Enum.reduce(children(node), fun.(node, acc), &reduce(&1, &2, fun))

  @doc "I am the rows `pred` reads, each once, in the order it writes them."
  @spec reads(pred()) :: [row_ref()]
  def reads(pred) do
    pred
    |> reduce([], fn node, acc -> if(r = read(node), do: [elem(r, 0) | acc], else: acc) end)
    |> Enum.reverse()
    |> Enum.uniq()
  end

  @doc "I am the rows a linked `pred` reads through as pointers, each once, in order."
  @spec pointer_reads(pred()) :: [pos_integer()]
  def pointer_reads(pred) do
    pred |> pointer_derefs() |> Enum.map(&elem(&1, 1)) |> Enum.uniq() |> Enum.sort()
  end

  @doc "I am the {value row, pointer row} of every composed read, each once, in order."
  @spec pointer_derefs(pred()) :: [{pos_integer(), pos_integer()}]
  def pointer_derefs(pred) do
    pred
    |> reduce([], fn node, acc ->
      case read(node) do
        {i, {:at, {:cell, j}, 1, 0}} -> [{i, j} | acc]
        _other -> acc
      end
    end)
    |> Enum.uniq()
    |> Enum.sort()
  end
end
