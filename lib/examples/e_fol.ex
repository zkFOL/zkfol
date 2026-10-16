defmodule Examples.EFol do
  @moduledoc "I am the standard relations' evidence: a program leans on them by name."

  use ExExample
  use Zkfol.Lang

  import ExUnit.Assertions

  alias Examples.ESudoku
  alias Examples.EUser
  alias Zkfol.Al
  alias Zkfol.Alloc
  alias Zkfol.Ast
  alias Zkfol.Derivation
  alias Zkfol.Pipeline
  alias Zkfol.Prover
  alias Zkfol.Semantics
  alias Zkfol.Statement
  alias Zkfol.Uair

  defrel counted(xs) do
    length(xs, n)
    each(xs, between(1, n))
  end

  defrel joined(zs) do
    append([1, 2], [3], zs)
  end

  defrel columns_apart(x) do
    column(x, cols)
    each(cols, permutation(9))
  end

  defrel literal_columns(cs) do
    column([[1, 2], [3, 4]], cs)
  end

  defrel there_and_back(x) do
    column(x, cs)
    column(cs, back)
    each(back, permutation(9))
  end

  defrel bumped(ys) do
    Zkfol.FOL.map([1, 2, 3], Examples.EUser.succ(), ys)
  end

  defrel rising([_last])

  defrel rising([a, b | t]) do
    a < b
    rising([b | t])
  end

  @doc "A call or a passed relation written with its module is that module's."
  @spec qualified_map() :: Statement.t()
  example qualified_map do
    [{_head, [{:call, {Zkfol.FOL, :map}, [_, {:papply, {EUser, :succ}, []} | _]}]}] =
      bumped().clauses

    assert Enum.take(Zkfol.stream(bumped(), [:_]), 1) == [[[2, 3, 4]]]

    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [bumped()], args: [:_]})

    assert Zkfol.Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  @spec ranged() :: Statement.t()
  example ranged do
    assert Enum.to_list(Zkfol.stream(counted(), [[3, 1, 2]])) == [[[3, 1, 2]]]
    assert Enum.to_list(Zkfol.stream(counted(), [[0, 1, 2]])) == []
    assert Enum.to_list(Zkfol.stream(counted(), [[4, 1, 2]])) == []

    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [counted()], args: [[3, 1, 2]]})

    assert Zkfol.Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  @spec concatenation() :: Statement.t()
  example concatenation do
    assert Enum.take(Zkfol.stream(joined(), [:_]), 1) == [[[1, 2, 3]]]

    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [joined()], args: [:_]})

    statement
  end

  @doc "I infer a permutation's size from its list; a missing value cannot form a permutation."
  @spec permutation_size() :: Derivation.t()
  example permutation_size do
    relation = Zkfol.Prims.permutation()
    {:ok, derivation} = Al.derived(relation, [:_, [3, 1, 2]])
    assert Derivation.root(derivation, :permutation) == {:permutation, [3, [3, 1, 2]]}

    for {n, cells} <- [{3, [1, 2]}, {2, [1, 2, 3]}, {1, []}, {-1, []}] do
      assert {:error, {:no_answer, _detail}} = Al.derived(relation, [n, cells])
      predicate = Ast.permutation(n, cells)
      assert Semantics.eval(predicate, 1, 1, fn _row, _column -> :error end) != 0
    end

    assert {:ok, _empty} = Al.derived(relation, [0, []])
    assert Semantics.eval(Ast.permutation(0, []), 1, 1, fn _row, _column -> :error end) == 0
    derivation
  end

  @doc "A row of the bank is a column of the grid, so the transpose lays no bank of its own."
  @spec transposed_columns() :: Statement.t()
  example transposed_columns do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [columns_apart()], args: [hd(ESudoku.act())]})

    assert Alloc.regions(Statement.alloc(statement)) == ["columns_apart x": 9, in: 2]
    statement
  end

  @doc "An index into a bank opens the nine values at that column; the groups stay private."
  @spec opened_column() :: Prover.Report.t()
  example opened_column do
    {:ok, statement} = Statement.opened(transposed_columns(), [{:columns_apart, :x, 9}])
    claims = Statement.claims(statement)

    {:ok, uair} = Uair.emit(Statement.pred(statement), Statement.witness(statement), claims)

    assert {:ok, claims} = Uair.claimed(uair)

    assert for({"columns_apart.x", value} <- claims, do: value) ==
             hd(hd(ESudoku.act()))

    [%{columns: columns, selections: selections}] = uair.selected_lookups
    assert Enum.all?(columns, &(&1 >= uair.num_public))
    assert length(selections) == 9

    {:ok, report, _id} = Prover.prove_uair(uair, name: :opened_column)
    report
  end

  @doc "A reading is cells like any other, so a call handed one reads it again, laying nothing."
  @spec chained_columns() :: Statement.t()
  example chained_columns do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [there_and_back()], args: [hd(ESudoku.act())]})

    assert Alloc.regions(Statement.alloc(statement)) == ["there_and_back x": 9, in: 2]
    refute :column in Alloc.names(Statement.alloc(statement))
    statement
  end

  @doc "A relation reading a cell's value is no rearrangement: `rising` and its bank are laid."
  @spec a_read_value_is_laid() :: [atom()]
  example a_read_value_is_laid do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [rising()], args: [[1, 2, 3]]})

    names = Alloc.names(Statement.alloc(statement))

    assert :rising in names
    assert :"rising a1" in names
    names
  end

  @doc "A literal transpose computes its output; its source needs no bank or called member."
  @spec laid_transpose() :: Statement.t()
  example laid_transpose do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [literal_columns()], args: [:_]})

    alloc = Statement.alloc(statement)
    assert Alloc.names(alloc) == [:literal_columns, :"literal_columns cs"]
    assert Zkfol.Semantics.valid?(Statement.pred(statement), Statement.witness(statement))

    assert {:ok, %Prover.Report{}, _id} =
             Prover.prove(Statement.pred(statement), Statement.witness(statement))

    statement
  end
end
