defmodule Zkfol.Phi.Place do
  @moduledoc """
  I describe scalar accesses, heap terms and declared array views.

  A view names its bank, its head column and the declared dimensions
  of each element. Its outer sequence ends at column one. A constant head gives a
  fixed length; a head relative to X or a pointer reads the bank's presence row.
  Every element has a complete layout when the view is created. Matching slices
  that layout; there is no inferred or partially known element shape.

  ### Public API

  - `is_laid/1`: recognize an array view.
  - `slice/2`, `shifted/2`, `count/1`, `elements/1`: read a view and its suffixes.
  - `cells/3`: lay declared dimensions over scalar accesses.
  - `presence/1`: read a view's presence cell.
  - `scalar?/1`, `affine/1`: recognize scalar accesses and affine expressions.
  - `consed/2`: reconstruct a peeled view or retain a pair.
  - `plain/3`, `output/2`: decide a parameter's access and ownership together.
  - `node_of/1`, `read/2`: realize terms and read their heap fields.
  """
  use TypedStruct
  alias Zkfol.Ast

  typedstruct module: View, enforce: true do
    @moduledoc "I am a bank view with a head address and fully declared element dimensions."
    field(:bank, atom())
    field(:head, Ast.address())
    field(:dimensions, [non_neg_integer()])
  end

  typedstruct module: Binding, enforce: true do
    @moduledoc "I pair an access with its allocation; :none borrows existing storage."
    field(:value, Zkfol.Phi.Place.t())
    field(:allocation, Zkfol.Alloc.allocation())
  end

  @type field :: :tag | :value | :head | :tail
  @type t ::
          Ast.term_t()
          | View.t()
          | {:node, Ast.term_t()}
          | [t()]
          | {:pair, t(), t()}
          | {:rel, atom(), [t()]}
          | {:count, integer(), Ast.term_t()}
          | {:fresh, Ast.row_ref()}
          | :fresh

  @doc "I recognize a declared array view."
  defguard is_laid(value) when is_struct(value, View)

  @doc "I recognize scalar data and scalar accesses."
  @spec scalar?(t()) :: boolean()
  def scalar?(value) when is_integer(value) or value == :x, do: true

  def scalar?(value) when is_tuple(value) and elem(value, 0) in [:cell, :count, :add, :mul],
    do: true

  def scalar?(_value), do: false

  @doc "I read one element using the view's declared dimensions."
  @spec slice(View.t(), integer()) :: t()
  def slice(%View{bank: bank, head: head, dimensions: dimensions}, i) do
    column = shifted_by(head, i)
    cells(dimensions, 1, &at({bank, &1}, column))
  end

  @doc "I lay nested dimensions over a function that names each scalar cell."
  @spec cells([non_neg_integer()], non_neg_integer(), (non_neg_integer() -> t())) :: t()
  def cells([], first, at), do: at.(first)

  def cells([n | inner], first, at) do
    stride = Enum.product(inner)
    for i <- 0..(n - 1)//1, do: cells(inner, first + i * stride, at)
  end

  @doc "I return a view's fixed outer length, or nil when its head moves."
  @spec count(t()) :: non_neg_integer() | nil
  def count(%View{head: {:at, :x, 0, n}}), do: n - 1
  def count(_value), do: nil

  @doc "I expose a fixed view's elements in source order."
  @spec elements(View.t()) :: [t()]
  def elements(view) do
    case count(view) do
      nil -> throw({:refused, {:unliftable_term, %{term: view}}})
      n -> Enum.map(0..(n - 1)//1, &slice(view, &1))
    end
  end

  @doc "I read a view's presence row at its head."
  @spec presence(View.t()) :: Ast.term_t()
  def presence(%View{bank: bank, head: head}), do: at({:in, bank}, head)

  @doc "I return the view past its first i elements."
  @spec shifted(View.t(), integer()) :: View.t()
  def shifted(view, i), do: %{view | head: shifted_by(view.head, i)}

  @doc "I give back {m, a} for a scalar place m * X + a; other places have no affine form."
  @spec affine(t()) :: {integer(), integer()} | nil
  def affine(:x), do: {1, 0}
  def affine(q) when is_integer(q), do: {0, q}
  def affine({:count, _q, cell}), do: affine(cell)

  def affine({:add, a, b}) do
    case {affine(a), affine(b)} do
      {{m, k}, {0, q}} -> {m, k + q}
      _apart -> nil
    end
  end

  def affine({:mul, a, q}) when is_integer(q) do
    case affine(a) do
      {m, k} -> {m * q, k * q}
      nil -> nil
    end
  end

  def affine(_place), do: nil

  @doc "I return the list a head and tail were peeled from, when the tail is that list past its head; otherwise their pair."
  @spec consed(t(), t()) :: t()
  def consed(head, tail) when is_laid(tail) do
    if slice(tail, -1) == head,
      do: shifted(tail, -1),
      else: {:pair, head, tail}
  end

  def consed(head, tail), do: {:pair, head, tail}

  @doc """
  I place an incoming parameter and state which storage it owns. Structures and private
  counts own cells; a passed relation owns its captures; other accesses are borrowed.
  A fresh parameter has no binding until matching establishes its representation.
  """
  @spec plain(t(), Ast.row_ref(), boolean()) :: Binding.t() | nil
  def plain(_form, ref, true), do: output([], ref)
  def plain(:fresh, _ref, false), do: nil
  def plain({:fresh, _unplaced}, _ref, false), do: nil
  def plain({:count, q, _cell}, ref, false), do: output(q, ref)

  def plain({:rel, p, fixed}, {name, {:param, sym}}, false) do
    rows = for k <- 1..length(fixed)//1, do: {name, {:own, {:"#{sym}.#{k}", []}}}
    %Binding{value: {:rel, p, Enum.map(rows, &Ast.cell/1)}, allocation: {:rel, p, rows}}
  end

  def plain(form, ref, false)
      when is_integer(form) or is_list(form) or is_laid(form) or
             (is_tuple(form) and elem(form, 0) in [:node, :pair]),
      do: output(form, ref)

  def plain(:x, _ref, false), do: %Binding{value: :x, allocation: {:column, 0}}

  def plain({:add, :x, offset} = form, _ref, false),
    do: %Binding{value: form, allocation: {:column, offset}}

  def plain(form, _ref, false), do: %Binding{value: form, allocation: :none}

  @doc "I give a resolved output its own cell or term identity; relation values share their captures."
  @spec output(t(), Ast.row_ref()) :: Binding.t()
  def output(value, ref) when is_integer(value),
    do: %Binding{value: {:count, value, Ast.cell(ref)}, allocation: {:cell, ref}}

  def output(value, ref)
      when is_list(value) or is_laid(value) or
             (is_tuple(value) and elem(value, 0) in [:node, :pair]),
      do: %Binding{value: {:node, Ast.cell(ref)}, allocation: {:node, ref}}

  def output({:rel, _p, _fixed} = value, _ref), do: %Binding{value: value, allocation: :none}

  def output(_value, ref) do
    %Binding{value: Ast.cell(ref), allocation: {:cell, ref}}
  end

  @doc "I return the node realizing a place: itself when it is one, the empty list's, or a row named by it."
  @spec node_of(t() | term()) :: {:node, Ast.term_t()}
  def node_of(node = {:node, _id}), do: node
  def node_of([]), do: {:node, 1}
  def node_of(place), do: {:node, Ast.cell({Zkfol.Nodes, {:node, place}})}

  @doc "I read one field of a node: its tag, value, head or tail, through the staging row when its id is no row."
  @spec read(field(), Ast.term_t()) :: Ast.term_t()
  def read(field, {:cell, row}), do: Ast.cell({Zkfol.Nodes, field}, row)
  def read(field, id), do: Ast.cell({Zkfol.Nodes, field}, {Zkfol.Nodes, {:read, id}})

  @spec at(Ast.row_ref(), Ast.address()) :: Ast.term_t()
  defp at(row, {:at, base, m, a}), do: Ast.at(row, base, m, a)

  @spec shifted_by(Ast.address(), integer()) :: Ast.address()
  defp shifted_by({:at, base, m, a}, i), do: Ast.address(base, m, a - i)
end
