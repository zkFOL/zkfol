defmodule Zkfol.Array do
  @moduledoc """
  I declare a finite array's dimensions and give its cells a compact bank.

  A root bank runs its outer dimension along columns and inner dimensions across rows.
  Local arrays keep all their cells on the calling member’s column.
  Every rank uses the same view; reading an element expands its declared dimensions.
  Matching and transpose share these accesses without copying element data.
  The dimensions are compiler input. Element values only enter through AL and Lay.

  ### Public API

  - `of/1`: read static dimensions from an array goal.
  - `known?/2`: recognize an existing view with those dimensions.
  - `local/4`: allocate per-call cells sourced from an array goal.
  - `bind/2`: allocate a declared array parameter.
  """
  use TypedStruct
  alias Zkfol.{Alloc, Ast}
  alias Zkfol.Phi.{Place, Walk}
  alias Zkfol.Phi.Place.{Binding, View}

  typedstruct enforce: true do
    field(:dimensions, [non_neg_integer()])
  end

  @doc "I read the static, nonnegative dimensions of an array goal."
  @spec of(term()) :: t()
  def of(dimensions) do
    unless dimensions?(dimensions),
      do: throw({:refused, {:array_shape, %{dimensions: dimensions}}})

    %__MODULE__{dimensions: dimensions}
  end

  defp dimensions?([]), do: true
  defp dimensions?([n | rest]) when is_integer(n) and n >= 0, do: dimensions?(rest)
  defp dimensions?(_other), do: false

  @doc "I check declared dimensions against an existing view or literal cells."
  @spec known?(t(), Zkfol.Phi.Value.t()) :: boolean()
  def known?(%__MODULE__{dimensions: dimensions}, value), do: matches?(dimensions, value)

  defp matches?([n | inner], %View{dimensions: inner} = view), do: Place.count(view) == n

  defp matches?(dimensions, {:pair, head, tail}), do: matches?(dimensions, [head | tail])

  defp matches?([0 | _inner], []), do: true

  defp matches?([n | inner], [head | tail]) when n > 0,
    do: matches?(inner, head) and matches?([n - 1 | inner], tail)

  defp matches?([], value), do: Place.scalar?(value)
  defp matches?(_dimensions, _value), do: false

  @doc "I give a local array its own cells at each call's column."
  @spec local(t(), Ast.row_ref(), Alloc.Source.t(), Walk.t()) :: {Zkfol.Phi.Value.t(), Walk.t()}
  def local(%__MODULE__{dimensions: dimensions}, {owner, {:param, name}}, source, walk) do
    access = Place.cells(dimensions, 0, &Ast.cell({owner, {:own, {name, &1}}}))
    rows = for {:cell, row} <- List.flatten(List.wrap(access)), do: row
    slot = %Alloc.Slot{name: name, allocation: {:record, rows}, source: source}
    {access, %{walk | slots: walk.slots ++ [slot]}}
  end

  @doc "I allocate a finite array, retaining its source parameter as the bank producer."
  @spec bind(t(), Ast.row_ref()) :: Walk.t()
  def bind(%__MODULE__{dimensions: []}, ref),
    do: Walk.bind(%Walk{}, ref, %Binding{value: Ast.cell(ref), allocation: {:cell, ref}})

  def bind(%__MODULE__{dimensions: [n | inner]}, ref) do
    bank = Alloc.Bank.of(ref)
    head = Ast.address(:x, 0, n + 1)

    view = %View{bank: bank, head: head, dimensions: inner}
    Walk.bind(%Walk{}, ref, %Binding{value: view, allocation: {:bank, bank, n}})
  end
end
