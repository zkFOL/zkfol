defmodule Zkfol.Phi.Match do
  @moduledoc """
  I match source terms against values and add the constraints the match needs.

  A value is a scalar expression, a heap term `{:node, id}`, a view of a walked array, a
  pair or `[]`, or a passed relation with the cells of its fixed arguments.

  | pattern    | scalar `e` | walked array            | heap term `i`                |
  |------------|------------|-------------------------|------------------------------|
  | number `q` | `e = q`    | dead                    | `value[i] = q`               |
  | `[]`       | dead       | `in = 0`                | `i = 1`                      |
  | `[h | t]`  | dead       | `in = 1`, first, rest   | `tag[i] = 2`, head, tail     |

  A name is bound the first time it is matched. Matched again, its value is equated with
  the new one.

  ### Public API

  - `matches/2`: match terms against values.
  - `equal/3`: constrain two terms to be equal.
  - `value/2`: the value of a term whose names are all bound.
  - `scalar/1`, `cells/1`: read a value as a number, or as a list of cells.
  - `frame/2`: a member's value as seen from a call at an address.
  """

  alias Zkfol.Ast
  alias Zkfol.Lang.Term
  alias Zkfol.Phi.{Place, Walk}
  alias Zkfol.Phi.Place.View
  alias Zkfol.Unfold

  @type value ::
          Ast.term_t()
          | {:node, Ast.term_t()}
          | View.t()
          | {:pair, value(), value()}
          | []
          | {:rel, atom(), [value()]}

  @typedoc "The walk after a match, or `:dead` when the match cannot hold."
  @type result :: Walk.t() | :dead

  @typep env :: %{Unfold.name() => value()}

  @doc "I am the value of a term whose names are all bound."
  @spec value(Term.t(), env()) :: value()
  def value({:var, v}, env) do
    case env do
      %{^v => value} -> value
      _unbound -> throw({:refused, {:unbound_variable, %{goals: [v]}}})
    end
  end

  def value(q, _env) when is_integer(q), do: q
  def value(:len, _env), do: Ast.len()
  def value(nil, _env), do: []
  def value({:cons, h, t}, env), do: {:pair, value(h, env), value(t, env)}
  def value({:add, a, b}, env), do: Ast.add(scalar(value(a, env)), scalar(value(b, env)))
  def value({:mul, a, b}, env), do: Ast.mul(scalar(value(a, env)), scalar(value(b, env)))
  def value({:papply, p, fixed}, env), do: {:rel, p, Enum.map(fixed, &value(&1, env))}

  @doc "I read a value as a number and refuse a list."
  @spec scalar(value()) :: Ast.term_t()
  def scalar({:node, id}), do: Place.read(:value, id)

  def scalar(value) do
    if structure?(value) or is_struct(value, View),
      do: throw({:refused, {:unliftable_term, %{term: value}}}),
      else: value
  end

  @doc "I read a list value as nested lists of cells."
  @spec cells(value()) :: [term()] | Ast.term_t()
  def cells({:pair, h, t}), do: [cells(h) | cells(t)]
  def cells([]), do: []
  def cells(value), do: scalar(value)

  @doc "I am a member's value as seen from a call through `pointer`."
  @spec frame(value(), Ast.address()) :: value()
  def frame({:node, id}, pointer), do: {:node, frame(id, pointer)}
  def frame({:rel, p, fixed}, pointer), do: {:rel, p, Enum.map(fixed, &frame(&1, pointer))}
  def frame({:cell, ref}, {:at, {:cell, row}, 1, 0}), do: Ast.cell(ref, row)

  @doc "I constrain `a` and `b` to be equal: the side whose names are all bound is the value."
  @spec equal(Term.t(), Term.t(), Walk.t()) :: result()
  def equal(a, b, walk) do
    if Enum.all?(Term.names(a), &is_map_key(walk.env, &1)),
      do: match(b, value(a, walk.env), walk),
      else: match(a, value(b, walk.env), walk)
  catch
    {:refused, {:unbound_variable, _name}} ->
      throw({:refused, {:unbound_variable, %{goals: [{:eq, a, b}]}}})
  end

  @doc "I match each term against its value and stop at the first `:dead`."
  @spec matches([{Term.t(), value()}], Walk.t()) :: result()
  def matches(pairs, walk),
    do: Walk.each(pairs, walk, fn {term, value}, walk -> match(term, value, walk) end)

  @spec match(Term.t(), value(), Walk.t()) :: result()
  defp match({:var, v}, value, walk) do
    case walk.env do
      %{^v => bound} -> equate(bound, value, walk)
      env -> %{walk | env: Map.put(env, v, value)}
    end
  end

  defp match(nil, value, walk), do: ended(value, walk)

  defp match({:cons, h, t}, value, walk) do
    with {head, tail, walk} <- peel(value, walk), do: matches([{h, head}, {t, tail}], walk)
  end

  defp match(term, value, walk), do: equate(value(term, walk.env), value, walk)

  @spec equate(value(), value(), Walk.t()) :: result()
  defp equate(a, a, walk), do: walk
  defp equate([], b, walk), do: ended(b, walk)

  defp equate({:pair, h, t}, b, walk) do
    with {head, tail, walk} <- peel(b, walk), do: equates([{h, head}, {t, tail}], walk)
  end

  defp equate({:rel, p, a}, {:rel, p, b}, walk) when length(a) == length(b),
    do: equates(Enum.zip(a, b), walk)

  defp equate({:node, a}, {:node, b}, walk), do: Walk.constrain(walk, [Ast.eq(a, b)])

  defp equate({:node, id}, view = %View{}, walk),
    do: Walk.constrain(walk, [Ast.eq(id, elem(Place.node_of(view), 1))])

  defp equate(a, b, walk) do
    cond do
      structure?(b) or match?({:node, _}, b) -> equate(b, a, walk)
      structure?(a) or is_struct(a, View) or is_struct(b, View) -> :dead
      match?({:node, _}, a) -> Walk.constrain(walk, Ast.folded(Ast.eq(scalar(a), b)))
      is_integer(a) and is_integer(b) -> :dead
      true -> Walk.constrain(walk, [Ast.eq(a, b)])
    end
  end

  @spec equates([{value(), value()}], Walk.t()) :: result()
  defp equates(pairs, walk), do: Walk.each(pairs, walk, fn {a, b}, walk -> equate(a, b, walk) end)

  @spec structure?(value()) :: boolean()
  defp structure?(value),
    do: value == [] or (is_tuple(value) and elem(value, 0) in [:pair, :rel])

  # The first element and the rest of a list value.
  @spec peel(value(), Walk.t()) :: {value(), value(), Walk.t()} | :dead
  defp peel({:pair, h, t}, walk), do: {h, t, walk}

  defp peel({:node, id}, walk) do
    head = {:node, Place.read(:head, id)}
    tail = {:node, Place.read(:tail, id)}
    {head, tail, Walk.constrain(walk, [Ast.eq(Place.read(:tag, id), 2)])}
  end

  # A view at a fixed column knows how many elements are left; a moving one reads the
  # bank's presence.
  defp peel(view = %View{}, walk) do
    case Place.count(view) do
      0 -> :dead
      nil -> peeled(view, Walk.constrain(walk, [Ast.eq(Place.presence(view), 1)]))
      _left -> peeled(view, walk)
    end
  end

  defp peel(_value, _walk), do: :dead

  @spec peeled(View.t(), Walk.t()) :: {value(), value(), Walk.t()}
  defp peeled(view, walk), do: {pairs(Place.slice(view, 0)), Place.shifted(view, 1), walk}

  # The value is the empty list.
  @spec ended(value(), Walk.t()) :: result()
  defp ended([], walk), do: walk
  defp ended({:node, id}, walk), do: Walk.constrain(walk, [Ast.eq(id, 1)])

  defp ended(view = %View{}, walk) do
    case Place.count(view) do
      0 -> walk
      nil -> Walk.constrain(walk, [Ast.eq(Place.presence(view), 0)])
      _left -> :dead
    end
  end

  defp ended(_value, _walk), do: :dead

  # Nested lists of cells as pair values.
  @spec pairs(term()) :: value()
  defp pairs(cells) when is_list(cells), do: List.foldr(cells, [], &{:pair, pairs(&1), &2})
  defp pairs(cell), do: cell
end
