defmodule Zkfol.Phi.Walk do
  @moduledoc """
  I am the state of compiling one clause: the value of each name, the constraints so far,
  the calls it makes and the rows it uses.

  ### Public API

  - `constrain/2`: add constraints.
  - `allocate/2`: give names a cell each.
  - `each/3`: run a step over items, stopping at a dead clause.
  """

  use TypedStruct
  use GtBridge.View

  alias GtBridge.Phlow.ColumnedList
  alias Zkfol.Alloc.{Site, Slot, Source}
  alias Zkfol.Ast
  alias Zkfol.Phi.Match
  alias Zkfol.Unfold

  typedstruct do
    field(:member, atom(), enforce: true)
    field(:clause, non_neg_integer(), enforce: true)
    field(:env, %{Unfold.name() => Match.value()}, default: %{})
    field(:eqs, [Ast.pred()], default: [])
    field(:sites, [Site.t()], default: [])
    field(:slots, [Slot.t()], default: [])
  end

  @doc "I add `eqs` to the clause's constraints."
  @spec constrain(t(), [Ast.pred()]) :: t()
  def constrain(walk = %__MODULE__{}, eqs), do: %{walk | eqs: eqs ++ walk.eqs}

  @doc "I run `step` over `items` and stop at the first `:dead`."
  @spec each([item], t(), (item, t() -> t() | :dead)) :: t() | :dead when item: var
  def each(items, walk = %__MODULE__{}, step) do
    Enum.reduce_while(items, walk, fn item, walk ->
      with walk = %__MODULE__{} <- step.(item, walk),
           do: {:cont, walk},
           else: (:dead -> {:halt, :dead})
    end)
  end

  @doc "I give each of `names` a cell in the clause's member, filled from the derivation."
  @spec allocate(t(), [Unfold.name()]) :: t()
  def allocate(walk = %__MODULE__{}, names), do: Enum.reduce(names, walk, &cell/2)

  # The name carries the calls it was unfolded through: the cell is filled from the
  # binding of the clause it came from.
  @spec cell(Unfold.name(), t()) :: t()
  defp cell(v = {calls, name}, walk) do
    ref = {walk.member, {:own, {name, calls ++ [walk.clause]}}}
    source = %Source{calls: calls, binding: {:variable, name}, clause: walk.clause}
    slot = %Slot{name: name, allocation: {:cell, ref}, source: source}
    %{walk | env: Map.put(walk.env, v, Ast.cell(ref)), slots: [slot | walk.slots]}
  end

  ############################################################
  #                            Views                         #
  ############################################################

  defview bindings_view(%Zkfol.Phi.Walk{env: env}, builder) do
    builder.columned_list()
    |> ColumnedList.title("Bindings")
    |> ColumnedList.priority(2)
    |> ColumnedList.items(Enum.sort(env))
    |> ColumnedList.column("Name", fn {name, _value} -> inspect(name) end)
    |> ColumnedList.column("Value", fn {_name, value} -> Zkfol.Face.inspected(value) end)
    |> ColumnedList.send(fn {_name, value} -> value end)
  end

  defview equations_view(%Zkfol.Phi.Walk{eqs: eqs}, builder) do
    builder.columned_list()
    |> ColumnedList.title("Equations")
    |> ColumnedList.priority(3)
    |> ColumnedList.items(Enum.reverse(eqs))
    |> ColumnedList.column("Equation", &Zkfol.Face.phi_text/1)
  end

  defview storage_view(%Zkfol.Phi.Walk{slots: slots, sites: sites}, builder) do
    builder.columned_list()
    |> ColumnedList.title("Storage")
    |> ColumnedList.priority(4)
    |> ColumnedList.items([{"Slots", slots}, {"Calls", Enum.reverse(sites)}])
    |> ColumnedList.column("What", fn {name, _value} -> name end)
    |> ColumnedList.column("Value", fn {_name, value} -> Zkfol.Face.inspected(value) end)
    |> ColumnedList.send(fn {_name, value} -> value end)
  end
end
