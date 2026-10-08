defmodule Examples.EFace do
  @moduledoc "I am the face's evidence: what a viewer reads, derived from the structs."

  use ExExample

  import ExUnit.Assertions

  alias Examples.EAl
  alias Examples.EUser
  alias Zkfol.Ast
  alias Zkfol.Face
  alias Zkfol.Interpretation
  alias Zkfol.Statement
  alias Zkfol.ZincPlus

  @doc "The slack row a guard range-checks reads :ranged; the rest are plain or shifted."
  @spec the_grid_feed_is_settled() :: %{atom() => term()}
  example the_grid_feed_is_settled do
    statement = EUser.fibonacci()

    {:ok, uair} =
      Zkfol.Uair.emit(
        Statement.pred(statement),
        Statement.witness(statement),
        Statement.claims(statement)
      )

    feed = Face.grid(uair)

    assert feed.len == 8
    assert hd(feed.columns) == Enum.reverse(Enum.map(1..8, &EUser.fib/1)) ++ List.duplicate(1, 8)
    assert feed.kinds == [:scheduled, :scheduled, :ranged] ++ List.duplicate(:scheduled, 6)
    assert Enum.all?(feed.columns, &(length(&1) == 16))
    assert feed.num_vars == 4

    assert length(feed.origins) == length(feed.columns)
    assert Enum.all?(feed.origins, &(String.starts_with?(&1, "C") or &1 in ["x", "ones"]))

    assert feed.degree == Ast.degree(Statement.pred(statement))
    assert feed.degree < ZincPlus.pcs_params().degree
    feed
  end

  @doc "I send an object through GT's result encoder and recover the same object."
  @spec bridged(object) :: object when object: var
  def bridged(object) do
    %{"exid" => id} = object |> GtBridge.Eval.encode_result() |> Jason.decode!()
    assert {:ok, ^object} = GtBridge.ObjectRegistry.get(id)
    GtBridge.ObjectRegistry.remove(id)
    object
  end

  @doc "What the judgement feed says is what the oracle and the lay say."
  @spec the_judgement_is_derived() :: %{atom() => term()}
  example the_judgement_is_derived do
    source = %Statement{rels: [EAl.hop_rel()], args: [5]}
    {:ok, statement, _trace} = Zkfol.Pipeline.run(EUser.plain(), source)
    pred = Statement.pred(statement)
    witness = Statement.witness(statement)
    len = Interpretation.len(witness)
    branches = pred |> Ast.conjuncts() |> Enum.flat_map(&Ast.branches/1)

    feed = Face.judgement(statement)

    raw = Face.judgement(%Statement{rels: [EAl.pick()]})
    assert Map.keys(raw) == Map.keys(feed)
    assert raw |> Map.values() |> Enum.all?(&(&1 == []))

    assert length(feed.labels) == length(branches)
    assert length(feed.sources) in [0, length(branches)]
    assert length(feed.rows) == Zkfol.Alloc.width(Statement.alloc(statement))

    for x <- 1..len do
      assert Enum.at(feed.holds, x - 1) == Zkfol.Semantics.holds?(pred, witness, x)
    end

    for branch <- feed.trees, column <- branch, goal <- column, node <- nodes(goal) do
      case Enum.map(node.children, &Map.get(&1, :role)) do
        ["left", "right"] ->
          [left, right] = node.children
          assert node.value == 0 == (left.value == right.value)

        ["pointer"] ->
          assert node.at == hd(node.children).value

        _other ->
          :ok
      end
    end

    assert feed.aims |> Enum.map(& &1.ptr) |> Enum.sort() == Ast.pointer_reads(pred)

    for %{ptr: ptr, from: from, to: to} <- feed.arrows do
      assert from in 1..len and to in 1..len
      if ptr, do: assert(Interpretation.at(witness, ptr, from) == to)
    end

    feed
  end

  @spec nodes(%{atom() => term()}) :: [%{atom() => term()}]
  defp nodes(node = %{children: children}), do: [node | Enum.flat_map(children, &nodes/1)]
end
