defmodule Examples.EUair do
  @moduledoc "I am the prover boundary's evidence: what it refuses, and the shapes it emits."

  use ExExample
  use Zkfol.Lang

  import ExUnit.Assertions

  alias Examples.EAst
  alias Examples.EFacts
  alias Examples.EForgery
  alias Examples.EUser
  alias Zkfol.Ast
  alias Zkfol.Interpretation
  alias Zkfol.Log
  alias Zkfol.Pipeline
  alias Zkfol.Prover
  alias Zkfol.Refusal
  alias Zkfol.Semantics
  alias Zkfol.Statement
  alias Zkfol.Uair
  alias Zkfol.ZincPlus

  defrel selected_when(0, cells)

  defrel selected_when(1, cells) do
    permutation(2, cells)
  end

  defrel apart(cells) do
    all_distinct(cells)
  end

  @doc "Distinctness takes scalar elements: rows are refused, not flattened."
  @spec distinct_rows_refused() :: Refusal.t()
  example distinct_rows_refused do
    assert {:error, refusal = {:unliftable_term, %{relation: :all_distinct}}} =
             Zkfol.Phi.compile(apart(), nil, [[[5, 9], [2, 7]]])

    refusal
  end

  @doc "Distinct private values prove through a sorted copy; a repeat is refused before the prover."
  @spec private_distinctness() :: Prover.Report.t()
  example private_distinctness do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [apart()], args: [[5, 9, 2]]})

    pred = Statement.pred(statement)
    witness = Statement.witness(statement)
    {:ok, uair} = Uair.emit(pred, witness)
    assert uair.selected_lookups == []
    assert [%ZincPlus.Permuted{pairs: pairs}] = uair.permuted_lookups
    assert length(pairs) == uair.len
    {:ok, report, _id} = Prover.prove_uair(uair, name: :apart)

    {:ok, claims} = Zkfol.Lay.claims(Statement.lay(statement), [1])
    [{_name, row, column} | _rest] = for {"apart.cells", _, _} = claim <- claims, do: claim
    repeated = EAst.tamper(witness, row, column, 9)
    refute Semantics.valid?(pred, repeated)
    assert {:error, {:witness_unsatisfies_schedule, _column}} = Uair.emit(pred, repeated)
    report
  end

  @doc "An inactive selection cannot replace the values an act opens."
  @spec selections_preserve_openings() :: [Prover.Report.t()]
  example selections_preserve_openings do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [selected_when()], args: [0, [2, 2]]})

    {:ok, opened} = Statement.opened(statement, [1, 2])

    assert {:error, {:selection_changes_claim, %{claim: "selected_when.cells"}}} =
             Uair.emit(
               Statement.pred(opened),
               Statement.witness(opened),
               Statement.claims(opened)
             )

    for enabled <- [0, 1] do
      {:ok, statement, _trace} =
        Pipeline.run(EUser.plain(), %Statement{rels: [selected_when()], args: [enabled, [2, 1]]})

      {:ok, opened} = Statement.opened(statement, [1, 2])
      claims = Statement.claims(opened)
      witness = Statement.witness(opened)
      expected = for {name, i, x} <- claims, do: {name, Interpretation.at(witness, i, x)}
      assert {:ok, uair} = Uair.emit(Statement.pred(opened), witness, claims)
      assert uair.claims == expected
      assert {:ok, report, _id} = Prover.prove_uair(uair)
      assert report.claims == expected
      report
    end
  end

  @doc "I take the plain route on purpose: the trace's own values need int768."
  @spec big_values_prove(pos_integer()) :: Log.Run.t()
  example big_values_prove(n \\ 98) do
    route = EUser.plain()
    ran = Zkfol.compile(%Statement{rels: [EFacts.factorial()], args: [n]}, pipeline: route)

    assert %Prover.Report{} = report = Log.report(Log.snapshot(), ran)
    assert report.backend =~ "int768"
    ran
  end

  @doc "Pointer bounds keep their degree as the trace grows; forged bounds fail at the prover."
  @spec pointer_bounds_have_fixed_degree() :: Uair.t()
  example pointer_bounds_have_fixed_degree do
    emitted =
      for len <- [8, 65] do
        values = Enum.to_list(1..len)
        pointers = tl(values) ++ [1]
        witness = Interpretation.new([values, pointers, pointers])
        {:ok, uair} = Uair.emit(Ast.eq(Ast.cell(1, 2), Ast.cell(3)), witness)
        assert {:ok, %Prover.Report{}, _id} = Prover.prove_uair(uair)
        uair
      end

    [short, long] = emitted
    assert short.degree == long.degree
    assert long.degree < ZincPlus.pcs_params().degree
    [%{row: pointer, bit_rows: [bit | _]}] = long.mode.reads
    [{^pointer, _limbs}, {slack, [low | _]}] = long.limbs

    for {row, value} <- [{pointer, 0}, {pointer, long.len + 1}, {slack, 2 ** 32}, {bit, 2}] do
      forged = List.update_at(long.columns, row, &List.replace_at(&1, 0, value))
      assert {:error, _refusal} = Prover.prove_uair(%{long | columns: forged})
    end

    # The final cube row is exempt from the polynomial, but the spelling stated a row back
    # holds it there, so a slack forged past 32 bits must carry its low limb with it.
    forged =
      for {cells, row} <- Enum.with_index(long.columns) do
        case row do
          ^slack ->
            List.replace_at(cells, -1, 2 ** 32)

          ^low ->
            List.update_at(cells, -1, &(&1 + 2 ** 32 - List.last(Enum.at(long.columns, slack))))

          _other ->
            cells
        end
      end

    assert {:error, {:prover_failed, _}} = Prover.prove_uair(%{long | columns: forged})

    assert {:ok, %Prover.Report{}, _id} =
             Prover.prove_uair(%{long | columns: forged, limbs: [hd(long.limbs)]})

    long
  end

  @doc "A branch reading a column back holds only where that column is in the trace."
  @spec reads_back_inside_the_trace() :: Uair.t()
  example reads_back_inside_the_trace do
    counted =
      Ast.disj([
        Ast.conj([Ast.eq(Ast.x(), 1), Ast.eq(Ast.cell(1), 0)]),
        Ast.eq(Ast.cell(1), Ast.add(Ast.at(1, :x, 1, -1), 1))
      ])

    {:ok, uair} = Uair.emit(counted, Interpretation.new([[0, 1, 2, 3, 4]]))
    assert {:ok, %Prover.Report{}, _id} = Prover.prove_uair(uair)

    # Counting from 96 at x = 1 would read 95 off the padding.
    [_count | rest] = uair.columns
    forged = %{uair | columns: [Enum.to_list(100..93//-1) | rest]}
    assert {:error, {:verifier_rejected, _}} = Prover.prove_uair(forged)
    uair
  end

  @doc "A full trace reserves padding: the backend's exempt final row is never an actual cell."
  @spec the_exempt_row_is_padding() :: Uair.t()
  example the_exempt_row_is_padding do
    {:ok, uair} = Uair.emit(Ast.eq(Ast.cell(1), 2), Interpretation.new([List.duplicate(2, 8)]))
    assert Uair.num_vars(uair) == 4
    assert [column] = uair.columns
    assert length(column) == 16
    actual = %{uair | columns: [List.replace_at(column, 7, 3)]}
    padding = %{uair | columns: [List.replace_at(column, 15, 3)]}
    assert {:error, {:verifier_rejected, _}} = Prover.prove_uair(actual)
    assert {:ok, %Prover.Report{}, _id} = Prover.prove_uair(padding)
    uair
  end

  @doc """
  I am the trace the forgery starts from: a mod holding its remainder below the
  modulus by a slack cell, six columns laid in a cube of eight.
  """
  @spec slacked_trace() :: Uair.t()
  example slacked_trace do
    statement = EUser.registers_mod(6)
    {:ok, uair} = Uair.emit(Statement.pred(statement), Statement.witness(statement))

    assert List.keymember?(uair.limbs, 5, 0)
    assert {:ok, %Prover.Report{}, _id} = Prover.prove_uair(uair, name: :slacked_trace)
    uair
  end

  @doc """
  I am the pair of verdicts the range declarations decide between. A remainder above
  its modulus keeps `e = m*q + r` true when the quotient falls by one, so the whole
  polynomial program holds of this trace; the slack and the quotient go negative for
  it, and the door carries them to the backend as built. Each moved cell carries its low
  limb, so every spelling holds too. Declared, the Word tables refuse the limbs.
  Dropped from the three columns the forgery moved, the same trace proves a remainder of
  7932 out of a modulus of 7919.
  """
  @spec forged_remainder_verdicts() :: {Refusal.t(), Prover.Report.t()}
  example forged_remainder_verdicts do
    uair = slacked_trace()
    modulus = 7919

    low = Map.new(uair.limbs, fn {column, [low | _]} -> {column, low} end)

    at = fn columns, column, move ->
      Enum.reduce([column, low[column]], columns, fn c, acc ->
        List.update_at(acc, c, &List.update_at(&1, 0, move))
      end)
    end

    columns =
      uair.columns
      |> at.(0, &(&1 + modulus))
      |> at.(2, &(&1 - 1))
      |> at.(5, &(&1 - modulus))

    forged = %{uair | columns: columns}
    assert hd(Enum.at(columns, 0)) >= modulus

    dropped = %{forged | limbs: Enum.reject(uair.limbs, &(elem(&1, 0) in [0, 2, 5]))}

    assert {:error, {:prover_failed, %{said: said}} = refused} =
             Prover.prove_uair(forged, name: :forged_remainder, unchecked: true)

    assert said =~ "Lookup"

    assert {:ok, %Prover.Report{} = proved, _id} =
             Prover.prove_uair(dropped, name: :dropped_remainder, unchecked: true)

    {refused, proved}
  end

  @doc """
  I am the standing audit of the range declarations. A naturality names a row and only
  a Word table over that row's column discharges it, so a row that reaches the emission
  undeclared is an obligation the proof has stopped carrying. A claimed row is carried
  by the private copy bonded to it, which holds the same cells; a declaration on the
  claim itself would discharge nothing, the lookup argument ranging over the witness
  trace and a claim riding outside it. Both counts stand at zero, over one statement
  of every shape the corpus writes. Where the declarations outrun the obligations it
  is the composed pointers, whose rows are declared as naturals too.
  """
  @spec declarations([{atom(), Statement.t()}]) ::
          [{atom(), non_neg_integer(), non_neg_integer()}]
  example declarations(corpus \\ EForgery.statements()) do
    for {name, statement} <- corpus do
      pred = Statement.pred(statement)
      {:ok, uair} = Uair.emit(pred, Statement.witness(statement), Statement.claims(statement))

      cells = &Enum.at(uair.columns, Enum.find_index(uair.rows, fn row -> row == &1 end))
      declared = for {column, _limbs} <- uair.limbs, do: Enum.at(uair.rows, column)
      claimed = Enum.take(uair.rows, uair.num_public)
      obliged = naturals(pred)
      carried = MapSet.new(declared, cells)

      lost =
        for {:cell, row} <- obliged,
            row not in declared,
            not (row in claimed and cells.(row) in carried),
            do: row

      assert lost == [], "#{name} obliges #{inspect(lost)} and declares nothing over it"
      assert length(obliged) <= length(declared), "#{name} declares fewer than it obliges"
      assert Enum.filter(declared, &(&1 in claimed)) == [], "#{name} declares over a claim"
      {name, length(obliged), length(declared)}
    end
  end

  @spec out_of_range_claim_is_refused() :: Refusal.t()
  example out_of_range_claim_is_refused do
    {:error, reason} =
      Prover.prove(Statement.pred(EUser.fibonacci()), Statement.witness(EUser.fibonacci()),
        claims: [{"n", 9, 1}]
      )

    assert {:claim_outside_witness, _} = reason
    reason
  end

  @spec negative_cell_is_refused() :: Refusal.t()
  example negative_cell_is_refused do
    {:ok, uair} =
      Uair.emit(Statement.pred(EUser.fibonacci()), Statement.witness(EUser.fibonacci()))

    negated = %{uair | columns: List.update_at(uair.columns, 0, &List.replace_at(&1, 0, -1))}

    {:error, reason} = ZincPlus.request(negated)
    assert {:witness_value_negative, %{value: -1}} = reason
    reason
  end

  @spec a_forged_presence_is_refused() :: Refusal.t()
  example a_forged_presence_is_refused do
    forged = EAst.tamper(Statement.witness(EUser.power()), 4, 4, 7)
    {:error, reason} = Prover.prove(Statement.pred(EUser.power()), forged)

    assert {:witness_unsatisfies_schedule, %{column: 4}} = reason
    reason
  end

  @doc "Cells a head spells at named columns are ties: no address, no bits, no Word."
  @spec named_cells_are_tied() :: Uair.t()
  example named_cells_are_tied do
    statement = EUser.open_tail()
    {:ok, uair} = Uair.emit(Statement.pred(statement), Statement.witness(statement))

    assert uair.limbs == []
    assert uair.mode == %Uair.Plain{}
    assert [%{selections: [_one]}] = uair.selected_lookups

    assert uair.point_ties == []
    assert Uair.num_cols(uair) == 5
    assert length(uair.program) == 99
    assert {:ok, %Prover.Report{}, _id} = Prover.prove_uair(uair, name: :named_cells)
    uair
  end

  # Every term the predicate obliges as a natural, each once. One naming a cell names
  # the row its lookup must land on; one over an expression is materialized onto a row
  # of its own, which only the emission knows.
  @spec naturals(Ast.pred()) :: [Ast.term_t()]
  defp naturals(pred) do
    pred
    |> Ast.reduce([], fn
      {:natural, term}, terms -> [term | terms]
      _node, terms -> terms
    end)
    |> Enum.uniq()
  end
end
