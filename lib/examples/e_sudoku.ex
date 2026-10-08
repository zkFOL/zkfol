defmodule Examples.ESudoku do
  @moduledoc "I am the sudoku's evidence: the game as a program over its grid."

  use ExExample
  use Zkfol.Lang

  import ExUnit.Assertions

  alias Examples.EUser
  alias Zkfol.Log
  alias Zkfol.Pipeline
  alias Zkfol.Prover
  alias Zkfol.Query
  alias Zkfol.Refusal
  alias Zkfol.Statement
  alias Zkfol.Uair
  alias Zkfol.Witness

  @solution [
    [9, 8, 7, 6, 5, 4, 3, 2, 1],
    [2, 4, 6, 1, 7, 3, 9, 8, 5],
    [3, 5, 1, 9, 2, 8, 7, 4, 6],
    [1, 2, 8, 5, 3, 7, 6, 9, 4],
    [6, 3, 4, 8, 9, 2, 1, 5, 7],
    [7, 9, 5, 4, 6, 1, 8, 3, 2],
    [5, 1, 9, 2, 8, 6, 4, 7, 3],
    [4, 7, 2, 3, 1, 9, 5, 6, 8],
    [8, 6, 3, 7, 4, 5, 2, 1, 9]
  ]

  @solution16 for r <- 0..15, do: for(c <- 0..15, do: rem(4 * rem(r, 4) + div(r, 4) + c, 16) + 1)

  defrel puzzle(
           1,
           [
             [_, _, _, _, _, _, _, _, _],
             [_, _, _, _, _, 3, _, 8, 5],
             [_, _, 1, _, 2, _, _, _, _],
             [_, _, _, 5, _, 7, _, _, _],
             [_, _, 4, _, _, _, 1, _, _],
             [_, 9, _, _, _, _, _, _, _],
             [5, _, _, _, _, _, _, 7, 3],
             [_, _, 2, _, 1, _, _, _, _],
             [_, _, _, _, 4, _, _, _, 9]
           ]
         )

  defrel puzzle(
           2,
           [
             [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16],
             [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 1, 2, 3, 4],
             [9, 10, 11, 12, 13, 14, 15, 16, 1, 2, 3, 4, 5, 6, 7, 8],
             [13, 14, 15, 16, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
             [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 1],
             [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 1, 2, 3, 4, 5],
             [10, 11, 12, 13, 14, 15, 16, 1, 2, 3, 4, 5, 6, 7, 8, 9],
             [14, 15, 16, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13],
             [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 1, 2],
             [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 1, 2, 3, 4, 5, 6],
             [11, 12, 13, 14, 15, 16, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
             [15, 16, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
             [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 1, 2, 3],
             [8, 9, 10, 11, 12, 13, 14, 15, 16, 1, 2, 3, 4, 5, 6, 7],
             [12, 13, 14, 15, 16, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
             [16, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
           ]
         )

  defrel solved(x) do
    puzzle(1, x)
    sudoku(x, 3)
  end

  defrel solved16(x) do
    puzzle(2, x)
    sudoku(x, 4)
  end

  defrel sudoku(xs, blocks) do
    length(xs, n)
    n = blocks ** 2
    blocks > 0
    each(xs, permutation(n))
    column(xs, cols)
    each(cols, permutation(n))
    boxes(blocks, xs, bs)
    each(bs, permutation(n))
    each(xs, all_labeled)
  end

  defrel boxes(n, rows, bs) do
    map(rows, chunk(n), runs)
    chunk(n, runs, bands)
    map(bands, column, stacks)
    map(stacks, mapcon, grouped)
    concat(grouped, bs)
  end

  defrel mapcon(xs, ys) do
    map(xs, concat, ys)
  end

  defrel all_labeled(xs) do
    each(xs, label)
  end

  @doc "I solve the clues with a free puzzle and return the answer as a statement."
  @spec answer() :: Statement.t()
  example answer do
    query = Zkfol.eval!(solved(), [:_], heap: 32_000_000)

    try do
      statement = Query.statement(query)
      assert statement.args == act()
      statement
    after
      Query.close(query)
    end
  end

  @doc "The rows, columns and boxes are a selection each: twenty-seven, on one table."
  @spec pattern_selected() :: Statement.t()
  example pattern_selected do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), answer())

    {:ok, uair} = Uair.emit(Statement.pred(statement), Statement.witness(statement))

    assert uair.limbs == []
    [%{values: values, selections: selections}] = uair.selected_lookups
    assert values == Enum.to_list(1..9)
    assert length(selections) == 27
    statement
  end

  @doc "Two cells opened say their eighteen values and nothing else of the answer."
  @spec opened_cells() :: Prover.Report.t()
  example opened_cells do
    {:ok, statement} =
      Statement.opened(pattern_selected(), [{:solved, :x, 9}, {:solved, :x, 8}])

    {:ok, uair} =
      Uair.emit(
        Statement.pred(statement),
        Statement.witness(statement),
        Statement.claims(statement)
      )

    assert for({"solved.x", value} <- uair.claims, do: value) ==
             Enum.concat(Enum.take(@solution, 2))

    {:ok, report, _id} = Prover.prove_uair(uair, name: :opened_cells)
    report
  end

  @doc "I am the columns of a grid, the bank `column` unifies against it."
  @spec columns([[pos_integer()]]) :: [[pos_integer()]]
  def columns(grid), do: Enum.zip_with(grid, & &1)

  @doc "I am the three by three boxes of a grid, band by band, as `boxes/0` derives them."
  @spec boxed([[pos_integer()]]) :: [[pos_integer()]]
  def boxed(grid),
    do:
      for(
        band <- Enum.chunk_every(grid, 3),
        stack <- 0..2,
        do: Enum.flat_map(band, &Enum.slice(&1, stack * 3, 3))
      )

  @doc "I am the act: the grid the relations check, and the prover's alone."
  @spec act([[pos_integer()]]) :: [[[pos_integer()]]]
  def act(grid \\ @solution), do: [grid]

  @doc "I am the sixteen-by-sixteen act, the completed grid `puzzle(2, …)` names."
  @spec act16() :: [[[pos_integer()]]]
  def act16, do: [@solution16]

  @doc "I am the solution with every digit relabelled, a sudoku again and another grid."
  @spec relabelled() :: [[pos_integer()]]
  def relabelled, do: for(row <- @solution, do: for(v <- row, do: 10 - v))

  @doc "The proof says a grid stands under the clues, and says nothing of which."
  @spec proof() :: Prover.Report.t()
  example proof do
    ran = Zkfol.compile(solved(), args: act())

    assert Enum.take(Zkfol.stream(solved(), act()), 1) == [act()]
    assert %Prover.Report{} = report = Log.report(Log.snapshot(), ran)
    assert report.claims == []
    report
  end

  @doc "A Latin square with shared boxes: refused over boxes the act never handed in."
  @spec a_shared_box_is_no_answer() :: Refusal.t()
  example a_shared_box_is_no_answer do
    latin = for i <- 0..8, do: for(j <- 0..8, do: rem(i + j, 9) + 1)

    assert held?(latin ++ columns(latin))
    refute held?(boxed(latin))

    {:error, Witness, refusal, []} =
      Pipeline.run(EUser.plain(), %Statement{rels: [sudoku()], args: [latin, 3]})

    assert {:no_answer, %{relation: :sudoku}} = refusal
    refusal
  end

  @spec held?([[pos_integer()]]) :: boolean()
  defp held?(groups), do: Enum.all?(groups, &(Enum.sort(&1) == Enum.to_list(1..9)))
end
