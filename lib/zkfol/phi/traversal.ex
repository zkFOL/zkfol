defmodule Zkfol.Phi.Traversal do
  @moduledoc """
  I plan unit-step traversals of declared arrays before the general compiler inlines them.

  A plan requires exactly an empty base and one self-call. Every changing argument
  must pass its own distinct array tail; other arguments must be unchanged static values.
  At least one array must change, and every array must have the same static outer extent.
  I infer no extents or scalar counters.
  Unsupported shapes return nil and remain ordinary calls.

  ### Public API

  - `plan/2`: recognize the traversal and return its explicit placement contract.
  - `parameters/3`: borrow the arrays at each traversal step.
  - `call/4`: select the planned self-edge, a new traversal, or ordinary compilation.
  """
  use TypedStruct
  alias Zkfol.Ast
  alias Zkfol.Lang.Rel
  alias Zkfol.Phi.{Place, Value, Walk}
  alias Zkfol.Phi.Place.Binding

  typedstruct enforce: true do
    field(:relation, atom())
    field(:arrays, [non_neg_integer()])
    field(:steps, {non_neg_integer(), integer()})
    field(:entry, Ast.address())
    field(:edge, [non_neg_integer()])
  end

  @doc "I recognize aligned, unit-step array recursion; all other programs return nil."
  @spec plan(Rel.t(), [Value.t()]) :: t() | nil
  def plan(%Rel{name: name, clauses: clauses}, values) when length(clauses) == 2 do
    Enum.find_value(Enum.with_index(clauses), fn {{head, body}, clause} ->
      calls = for {{:call, ^name, args}, goal} <- Enum.with_index(body), do: {args, goal}

      with [{args, goal}] <- calls,
           {base, []} <- Enum.at(clauses, 1 - clause),
           kinds = Enum.zip([base, head, args, values]) |> Enum.map(&parameter/1),
           false <- :unsupported in kinds,
           [_ | _] = arrays <- for({:array, i} <- Enum.with_index(kinds), do: i),
           tails = Enum.map(arrays, &Enum.at(args, &1)),
           true <- length(Enum.uniq(tails)) == length(tails),
           [n] when is_integer(n) and n >= 0 <-
             Enum.map(arrays, &extent(Enum.at(values, &1))) |> Enum.uniq() do
        %__MODULE__{
          relation: name,
          arrays: arrays,
          steps: {hd(arrays), -1},
          entry: Ast.address(:x, 0, n + 1),
          edge: [goal, clause]
        }
      else
        _unsupported -> nil
      end
    end)
  end

  def plan(_rel, _values), do: nil

  defp parameter({nil, {:cons, _head, {:var, tail}}, {:var, tail}, _value}), do: :array

  defp parameter({{:var, _}, {:var, name}, {:var, name}, value}),
    do: if(static?(value), do: :fixed, else: :unsupported)

  defp parameter(_other), do: :unsupported

  defp static?(q) when is_integer(q), do: true
  defp static?({:rel, _name, fixed}), do: Enum.all?(fixed, &static?/1)
  defp static?(_value), do: false

  defp extent(view = %Place.View{head: {:at, :x, 0, _head}}), do: Place.count(view)
  defp extent(_value), do: nil

  @doc "I bind traversed arrays at X and retain static arguments, preserving bank ownership."
  @spec parameters(t(), [Value.t()], [Ast.row_ref()]) ::
          Walk.t()
  def parameters(plan, values, refs) do
    declarations =
      for {{value, ref}, i} <- Enum.with_index(Enum.zip(values, refs)) do
        value = if i in plan.arrays, do: %{value | head: Ast.address(:x, 1, 0)}, else: value
        Walk.bind(%Walk{}, ref, %Binding{value: value, allocation: :none})
      end

    Enum.reduce(declarations, %Walk{}, &Walk.merge/2)
  end

  @doc "I select only the exact planned self-call; other sites get their own plan or none."
  @spec call(Rel.t(), [Value.t()], t() | nil, [term()]) ::
          Ast.address() | t() | nil
  def call(%Rel{name: name}, _values, %__MODULE__{relation: name, edge: site}, site),
    do: Ast.address(:x, 1, -1)

  def call(rel, values, _parent, _site), do: plan(rel, values)
end
