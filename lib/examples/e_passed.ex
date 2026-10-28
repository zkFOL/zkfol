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

  defrel add(k, x, y) do
    y = x + k
  end

  @doc "An equation's local name stays a variable even when a relation has the same name."
  @spec equation_local_name() :: Derivation.t()
  example equation_local_name do
    root =
      rel do
        local_number(x) do
          add = 3
          x = add + 1
        end
      end

    {:ok, derivation} = Al.derived(root, [:_])
    assert Derivation.root(derivation, :local_number) == {:local_number, [4]}
    derivation
  end

  defrel bound_callback(f, x, y) do
    f(x)
    add(1, x, y)
    f = natural()
  end

  @doc "A local or head callback binds in every goal order, including across another call."
  @spec callback_goal_order() :: [Lay.t()]
  example callback_goal_order do
    root = bound_callback()
    [{head, body}] = root.clauses

    for {params, args} <- [{head, [:_, 7, :_]}, {tl(head), [7, :_]}],
        a <- body,
        b <- body,
        b != a,
        c <- body,
        c not in [a, b] do
      rel = %{root | arity: length(params), clauses: [{params, [a, b, c]}]}
      {:ok, pred, alloc} = Phi.compile(rel, nil, args)
      {:ok, derivation} = Al.derived(rel, args)
      {:bound_callback, answer} = Derivation.root(derivation, :bound_callback)
      assert Enum.take(answer, -2) == [7, 8]
      lay = Lay.of(derivation, alloc)

      assert {:ok, %Prover.Report{}, _id} =
               Prover.prove(Alloc.link(pred, alloc), Lay.witness(lay))

      assert {:error, {:no_answer, _}} = Al.derived(rel, List.replace_at(args, -1, 9))
      lay
    end
  end

  defrel invoke(f, x, y), do: f(x, y)

  defrel captured_callback(k, x, y) do
    f.(x, y)
    f = invoke(add(k * k + 1))
  end

  @doc "Nested closures capture private arithmetic through equality and retain its constraints."
  @spec callback_captures() :: [Lay.t()]
  example callback_captures do
    root = captured_callback()
    {:ok, pred, alloc} = Phi.compile(root, nil, [2, 7, :_])
    linked = Alloc.link(pred, alloc)

    for {k, x} <- [{2, 7}, {5, 4}] do
      assert {:ok, ^pred, ^alloc} = Phi.compile(root, nil, [k, x, :_])
      {:ok, derivation} = Al.derived(root, [k, x, :_])
      assert Derivation.root(derivation, root.name) == {root.name, [k, x, k * k + x + 1]}
      lay = Lay.of(derivation, alloc)
      witness = Lay.witness(lay)
      assert {:ok, %Prover.Report{}, _id} = Prover.prove(linked, witness)
      {:ok, [{_name, row, column} | _presence]} = Lay.claims(lay, [3])
      refute Semantics.valid?(linked, EAst.tamper(witness, row, column, k * k + x))
      lay
    end
  end

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
    odd_last(n - 2, tail, out)
  end

  @doc "A nonunit scalar step works with an undeclared list in term storage."
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
    last_step(n - 1, tail, out)
  end

  defrel last_step(1, xs, out) do
    xs = [out]
  end

  defrel last_step(n, xs, out) do
    last_call(n, xs, out)
  end

  @doc "Mutually recursive calls share an undeclared list through term storage."
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
    loose_last(n - 1, tail, out)
  end

  defrel loose_last(n, [_head | tail], out) do
    loose_last(n - 2, tail, out)
  end

  @doc "Alternative bases and strides work without inferring the list length."
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
    last_at(n - 1, [next | tail], out)
    last_at(n - 2, tail, out)
  end

  @doc "Different bases and strides constrain the same list through ordinary calls."
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
