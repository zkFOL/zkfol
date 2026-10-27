defmodule Examples.EPassed do
  @moduledoc "I am the passed reading's evidence: a prim reads the same through a handed name."

  use ExExample
  use Zkfol

  import ExUnit.Assertions

  alias Examples.EAst
  alias Examples.EUser
  alias Zkfol.{Al, Alloc, Derivation, Lay, Prover}
  alias Zkfol.Phi
  alias Zkfol.Pipeline
  alias Zkfol.Semantics
  alias Zkfol.Statement

  defrel counted(xs) do
    each(xs, natural())
  end

  @spec passed_reading() :: Statement.t()
  example passed_reading do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [counted()], args: [[3, 0, 7]]})

    assert Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  defrel narrow(x) do
    all_distinct(x)
  end

  defrel pick(i, x, v) do
    nth(i, x, v)
  end

  @doc "One compiled read accepts different private indices and values, but rejects wrong answers."
  @spec cached_indexed_read() :: [Zkfol.Interpretation.t()]
  example cached_indexed_read do
    {:ok, empty, allocation} = Phi.compile(pick(), [pick()], [1, [], :_])
    fact = {:pick, [1, [], 10]}
    attempted = %Derivation{facts: [fact], clauses: [{fact, 0}]}
    witness = attempted |> Lay.of(allocation) |> Lay.witness()
    assert {:error, _refusal} = Prover.prove(Alloc.link(empty, allocation), witness)

    {:ok, pred, alloc} = Phi.compile(pick(), [pick()], [1, [10, 20], :_])
    linked = Alloc.link(pred, alloc)

    for {i, xs} <- [{1, [10, 20]}, {2, [10, 20]}, {1, [30, 40]}, {2, [30, 40]}] do
      {:ok, again, layout} = Phi.compile(pick(), [pick()], [i, xs, :_])
      assert Alloc.link(again, layout) == linked
      {:ok, derivation} = Al.derived(pick(), [i, xs, :_])
      assert Derivation.root(derivation, :pick) == {:pick, [i, xs, Enum.at(xs, i - 1)]}
      witness = derivation |> Lay.of(alloc) |> Lay.witness()
      assert {:ok, %Prover.Report{}, _id} = Prover.prove(linked, witness)

      for args <- [[i, xs, Enum.at(xs, 2 - i)], [0, xs, hd(xs)], [3, xs, hd(xs)]] do
        fact = {:pick, args}
        forged = %Derivation{facts: [fact], clauses: [{fact, 0}]}
        witness = forged |> Lay.of(alloc) |> Lay.witness()
        refute Semantics.valid?(linked, witness)
        assert {:error, _refusal} = Prover.prove(linked, witness)
      end

      witness
    end
  end

  defrel first(xs, out) do
    nth(1, xs, out)
  end

  @doc "A literal index selects a whole row."
  @spec first_row() :: Statement.t()
  example first_row do
    rows = [[10, 20], [30, 40]]

    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [first()], args: [rows, :_]})

    assert Derivation.root(Statement.derivation(statement), :first) == {:first, [rows, [10, 20]]}
    assert Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  @doc "A private index selects a row through nth's clauses."
  @spec picked_row() :: Statement.t()
  example picked_row do
    rows = [[10, 20], [30, 40]]

    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [pick()], args: [2, rows, :_]})

    assert Derivation.root(Statement.derivation(statement), :pick) == {:pick, [2, rows, [30, 40]]}
    assert Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  defrel odd_last(1, [out], out)

  defrel odd_last(n, [_head | tail], out) do
    n2 = n - 2
    odd_last(n2, tail, out)
  end

  @doc "A fractional stride has no bank length, so the list stays terms."
  @spec strided_last() :: Statement.t()
  example strided_last do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [odd_last()], args: [5, [10, 20, 30], :_]})

    assert Derivation.root(Statement.derivation(statement), :odd_last) ==
             {:odd_last, [5, [10, 20, 30], 30]}

    assert Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  defrel last_call(n, [_head | tail], out) do
    n1 = n - 1
    last_step(n1, tail, out)
  end

  defrel last_step(1, xs, out) do
    xs = [out]
  end

  defrel last_step(n, xs, out) do
    last_call(n, xs, out)
  end

  @doc "A callee whose extent is unknown leaves the caller's list as terms."
  @spec mutual_last() :: Statement.t()
  example mutual_last do
    rels = [last_call(), last_step()]

    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: rels, args: [3, [10, 20, 30], :_]})

    assert Derivation.root(Statement.derivation(statement), :last_call) ==
             {:last_call, [3, [10, 20, 30], 30]}

    assert Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  defrel loose_last(1, [out], out)
  defrel loose_last(1, [_head, out], out)

  defrel loose_last(n, [_head | tail], out) do
    n1 = n - 1
    loose_last(n1, tail, out)
  end

  defrel loose_last(n, [_head | tail], out) do
    n2 = n - 2
    loose_last(n2, tail, out)
  end

  @doc "Two bases and two strides that disagree on the length leave the list as terms."
  @spec loosely_stepped() :: Statement.t()
  example loosely_stepped do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [loose_last()], args: [3, [10, 20], :_]})

    assert Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  defrel last_at(5, [out], out)
  defrel last_at(6, [_head, out], out)

  defrel last_at(n, [_head, next | tail], out) do
    n1 = n - 1
    last_at(n1, [next | tail], out)
    n2 = n - 2
    last_at(n2, tail, out)
  end

  @doc "Different bases and strides that agree on length(xs) = n - 4 give one extent."
  @spec agreeing_bases() :: Statement.t()
  example agreeing_bases do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [last_at()], args: [7, [10, 20, 30], :_]})

    assert Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  defrel reads(xs, i, first, selected) do
    nth(1, [42], constant)
    constant = 42
    nth(1, xs, first)
    nth(i, xs, selected)
  end

  @doc "Stored terms share one read predicate across private indices, beside an optimized read."
  @spec stored_indexed_reads() :: [Lay.t()]
  example stored_indexed_reads do
    {:ok, pred, alloc} = Phi.compile(reads(), nil, [[9, [4, 5], 7], 1, :_, :_])
    linked = Alloc.link(pred, alloc)

    for {xs, i} <- [{[9, [4, 5], 7], 1}, {[11, [6, 8], 13], 3}] do
      assert {:ok, ^pred, ^alloc} = Phi.compile(reads(), nil, [xs, i, :_, :_])
      {:ok, derivation} = Al.derived(reads(), [xs, i, :_, :_])
      assert Derivation.root(derivation, :reads) == {:reads, [xs, i, hd(xs), Enum.at(xs, i - 1)]}
      lay = Lay.of(derivation, alloc)
      witness = Lay.witness(lay)
      assert Semantics.valid?(linked, witness)
      assert {:ok, %Prover.Report{}, _id} = Prover.prove(linked, witness)

      for {parameter, wrong} <- [{4, 1}, {2, 0}, {2, length(xs) + 1}] do
        {:ok, [{_name, row, column} | _cells]} = Lay.claims(lay, [parameter])

        forged = EAst.tamper(witness, row, column, wrong)

        refute Semantics.valid?(linked, forged)
        assert {:error, _refusal} = Prover.prove(linked, forged)
      end

      lay
    end
  end

  defrel total([], 0)

  defrel total([h | t], sum) do
    h > 0
    total(t, rest)
    sum = h + rest
  end

  defrel combined(xs, sum) do
    with_total(xs, total(), sum)
  end

  defrel with_total(xs, f, sum) do
    f([1, 2], a)
    total(xs, b)
    sum = a + b
  end

  @doc "A literal sum and a private list's sum compose, including when both calls return the same fact."
  @spec sums_compose() :: [Statement.t()]
  example sums_compose do
    for xs <- [[4, 5], [1, 2], [7, 8, 9]] do
      {:ok, statement, _trace} =
        Pipeline.run(EUser.plain(), %Statement{rels: [combined()], args: [xs, :_]})

      assert Derivation.root(Statement.derivation(statement), :combined) ==
               {:combined, [xs, 3 + Enum.sum(xs)]}

      assert {:ok, %Prover.Report{}, _id} =
               Prover.prove(Statement.pred(statement), Statement.witness(statement))

      statement
    end
  end
end
