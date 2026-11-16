defmodule Zkfol.Phi.Value do
  @moduledoc """
  I am the operations the unifier needs on a value: a place, a list of them,
  a passed relation, or nothing yet.

  ### Public API

  - `scalar/1`: the arithmetic reading of a value.
  - `elements/1`: its elements for a primitive operation.
  - `frame/2`: express a callee's value at its call address.
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
  I retain literal lists, numbers and relations. Scalar accesses leave the callee's
  parameter unresolved. Views addressed from X keep their bank; views addressed through
  pointers and pairs pass as nodes.
  """
  @spec handed(t()) :: t()
  def handed(node = {:node, _id}), do: node
  def handed(view = %Place.View{head: {:at, :x, _, _}}), do: view
  def handed(view = %Place.View{}), do: Place.node_of(view)
  def handed(pair = {:pair, _, _}), do: Place.node_of(pair)
  def handed(form) when is_list(form) or is_integer(form) or form == :fresh, do: form
  def handed({:rel, _name, _fixed} = form), do: form
  def handed(_scalar), do: :fresh

  @doc "I express a callee value at its call address in the caller."
  @spec frame(t(), frame()) :: t()
  # Recursive ancestors can be called before their parameter storage is completed.
  def frame({:fresh, ref}, frame), do: frame({:cell, ref}, frame)
  def frame({:node, id}, frame), do: {:node, frame(id, frame)}
  def frame({:rel, p, fixed}, frame), do: {:rel, p, Enum.map(fixed, &frame(&1, frame))}
  def frame(form, _frame) when is_integer(form) or form in [:fresh, []], do: form

  def frame(laid, frame) when Place.is_laid(laid),
    do: %{laid | head: reframed(laid.head, frame, laid)}

  def frame(cell, frame) do
    {row, address} = Ast.read(cell)
    {:at, base, m, a} = reframed(address, frame, cell)
    Ast.at(row, base, m, a)
  end

  # An address the frame cannot express refuses the value.
  @spec reframed(Ast.address(), frame(), t()) :: Ast.address()
  defp reframed(address, frame, value) do
    Ast.reframe(address, frame) || throw({:refused, {:unliftable_term, %{term: value}}})
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
