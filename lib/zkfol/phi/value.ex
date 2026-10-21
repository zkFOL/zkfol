defmodule Zkfol.Phi.Value do
  @moduledoc """
  I am the operations the unifier needs on a value: a place, a list of them,
  a passed relation, or nothing yet.

  ### Public API

  - `scalar/1`: the arithmetic reading of a value.
  - `elements/1`: its elements for a primitive operation.
  - `frame/2`, `unframe/2`: express values across a call's column frame.
  - `handed/1`: the value a callee is handed for a caller's value.
  """

  alias Zkfol.Ast
  alias Zkfol.Phi.Place

  require Place

  @typedoc "A scalar expression reads cells or reifies a predicate."
  @type scalar :: Ast.poly(Ast.ep_leaf() | {:reify, Ast.pred()} | Place.t())

  @typedoc "What a name holds: a place, or a scalar expression over places."
  @type t :: Place.t() | scalar()

  @typedoc "Where a call reaches: an affine frame of the column, or a pointer cell."
  @type frame :: Ast.address()

  @doc "I expose finite views to a primitive, preserving nested elements."
  @spec elements(t()) :: t()
  def elements(view) when Place.is_laid(view), do: Place.elements(view)
  def elements({:pair, h, t}), do: [elements(h) | elements(t)]
  def elements([h | t]), do: [elements(h) | elements(t)]
  def elements(form), do: form

  @doc """
  I retain literal lists, numbers, relations and affine scalar expressions.
  Other scalar accesses leave the callee's parameter unresolved. Views addressed
  from X keep their bank; views addressed through pointers and pairs pass as nodes.
  """
  @spec handed(t()) :: t()
  def handed(node = {:node, _id}), do: node
  def handed(view = %Place.View{head: {:at, :x, _, _}}), do: view
  def handed(view = %Place.View{}), do: Place.node_of(view)
  def handed(pair = {:pair, _, _}), do: Place.node_of(pair)
  def handed(form) when is_list(form) or is_integer(form) or form == :fresh, do: form
  def handed({:rel, _name, _fixed} = form), do: form
  def handed(form), do: if(Place.affine(form) != nil, do: form, else: :fresh)

  @doc "I express a callee value at its call address in the caller."
  @spec frame(t(), frame()) :: t()
  # Recursive ancestors can be called before their parameter storage is completed.
  def frame({:fresh, ref}, frame), do: frame({:cell, ref}, frame)
  def frame(form, {:at, :x, 1, 0}), do: form
  def frame({:node, id}, frame), do: {:node, frame(id, frame)}
  def frame({:pair, h, t}, frame), do: {:pair, frame(h, frame), frame(t, frame)}
  def frame([h | t], frame), do: [frame(h, frame) | frame(t, frame)]
  def frame({:rel, p, fixed}, frame), do: {:rel, p, Enum.map(fixed, &frame(&1, frame))}
  def frame(form, _frame) when is_integer(form) or form in [:fresh, []], do: form

  def frame(laid, frame) when Place.is_laid(laid),
    do: %{laid | head: reframed(laid.head, frame, laid)}

  def frame(form, frame) do
    Ast.postwalk(form, fn
      :x ->
        Ast.naming(frame)

      {:add, a, b} ->
        Ast.add(a, b)

      cell when is_tuple(cell) and elem(cell, 0) == :cell ->
        {row, address} = Ast.read(cell)

        case Ast.reframe(address, frame) do
          nil -> throw({:refused, {:unliftable_term, %{term: cell}}})
          {:at, base, m, a} -> Ast.at(row, base, m, a)
        end

      node ->
        node
    end)
  end

  # An address the frame cannot express refuses the value.
  @spec reframed(Ast.address(), frame(), t()) :: Ast.address()
  defp reframed(address, frame, value) do
    Ast.reframe(address, frame) || throw({:refused, {:unliftable_term, %{term: value}}})
  end

  @doc """
  I express the values a callee can retain in its own column frame. A list the frame
  cannot express keeps the caller's address; the callee re-heads it at its own extent.
  """
  @spec unframe(t(), frame()) :: t()
  def unframe(form, {:at, :x, 1, 0}), do: form

  def unframe(node = {:node, _id}, _frame), do: node

  def unframe(laid, frame) when Place.is_laid(laid) do
    case Ast.unframe(laid.head, frame) do
      nil -> laid
      address -> %{laid | head: address}
    end
  end

  def unframe(form, _frame) when is_list(form) or form == :fresh or elem(form, 0) == :rel,
    do: form

  def unframe(form, frame) do
    case Place.affine(form) do
      {0, q} ->
        q

      {m, a} ->
        case Ast.unframe(Ast.address(:x, m, a), frame) do
          nil -> :fresh
          local -> Ast.naming(local)
        end

      nil ->
        :fresh
    end
  end

  @doc "I read a scalar value, refusing structure where arithmetic requires a number."
  @spec scalar(t()) :: scalar()
  def scalar({:node, id}), do: Place.read(:value, id)
  def scalar({:fresh, ref}), do: throw({:waiting, [{:scalar, ref}]})

  def scalar(form)
      when Place.is_laid(form) or is_list(form) or
             (is_tuple(form) and elem(form, 0) in [:pair, :rel]),
      do: throw({:refused, {:unliftable_term, %{term: form}}})

  def scalar(form), do: form
end
