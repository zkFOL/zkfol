defmodule Zkfol.Lang.Term do
  @moduledoc """
  I am the surface term: a polynomial over the leaves a clause writes, and the goals its
  body writes over me.

  t    ::= q | t + t | t * t | len | var | nil | [t | t] | "s" | name(t, ...)
  goal ::= name(t, ...) | var(t, ...) | t = t | reify(goal)

  Scoped, a var is the clause's own and `name(t, ...)` a relation in scope with what it
  fixes. Names work like any normal Elixir name. A string is the bracket of its codepoints.
  """

  @type name :: atom() | {module(), atom()}

  @typedoc "What a term stands on: a name, the empty sequence, a bracket, a partial call, len."
  @type leaf ::
          {:var, atom()}
          | nil
          | :len
          | {:cons, t(), t()}
          | {:papply, name(), [t()]}

  @typedoc "A surface term: Figure 1's polynomial over my leaves."
  @type t :: Zkfol.Ast.poly(leaf())

  @typedoc "A goal of a clause body: a call, an equation, or an equation as a term."
  @type goal :: {:call, name() | {:var, atom()}, [t()]} | {:eq, t(), t()} | {:reify, goal()}

  @doc "I am the immediate children of a node: none for a leaf."
  @spec children(term()) :: [term()]
  def children({tag, t, u}) when tag in [:add, :mul, :cons, :eq], do: [t, u]
  def children({tag, _name, args}) when tag in [:papply, :call], do: args
  def children({:reify, goal}), do: [goal]
  def children(nodes) when is_list(nodes), do: nodes
  def children(_leaf), do: []

  @doc "I fold `fun` over every node, each parent before its children."
  @spec reduce(term(), acc, (term(), acc -> acc)) :: acc when acc: var
  def reduce(node, acc, fun),
    do: Enum.reduce(children(node), fun.(node, acc), &reduce(&1, &2, fun))

  @doc "I am the variable names a term carries, in the order it writes them."
  @spec names(term()) :: [atom()]
  def names(node) do
    node
    |> reduce([], fn
      {:var, name}, acc -> [name | acc]
      _node, acc -> acc
    end)
    |> Enum.reverse()
  end

  @doc "I am the relation a term passes and the arguments it fixes, nil where it passes none."
  @spec passed(t(), MapSet.t()) :: {name(), [t()]} | nil
  def passed({:papply, name, prefix}, _bound), do: {name, prefix}
  def passed({:var, name}, bound), do: if(not MapSet.member?(bound, name), do: {name, []})
  def passed(_term, _bound), do: nil

  @doc "I am the elements a closed bracket lists; a bracket open past a name lists none for sure."
  @spec closed(term()) :: [term()] | nil
  def closed(nil), do: []
  def closed({:var, _name}), do: nil

  def closed({:cons, head, tail}) do
    case closed(tail) do
      nil -> nil
      rest -> [head | rest]
    end
  end

  @doc "I say whether a term is a sequence: a bracket or the empty one."
  @spec sequence?(term()) :: boolean()
  def sequence?(nil), do: true
  def sequence?({:cons, _head, _tail}), do: true
  def sequence?(_term), do: false

  @doc "I say whether a head term names cells: a column, a pinned integer, or a bracket."
  @spec seatable?(term()) :: boolean()
  def seatable?({:var, _name}), do: true
  def seatable?(nil), do: true
  def seatable?({:cons, head, tail}), do: seatable?(head) and seatable?(tail)
  def seatable?(term), do: is_integer(term)
end
