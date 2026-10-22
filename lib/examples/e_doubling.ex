defmodule Examples.EDoubling do
  @moduledoc "I am the doubling rewrite's evidence: one predicate for every n."

  use ExExample

  import ExUnit.Assertions
  require Zkfol.Lang

  alias Examples.EUser
  alias Zkfol.Ast
  alias Zkfol.Doubling
  alias Zkfol.Interpretation
  alias Zkfol.Lang.Rel
  alias Zkfol.Pipeline
  alias Zkfol.Semantics
  alias Zkfol.Statement

  @mod 7919

  @spec rewritten_fibonacci(pos_integer()) :: Statement.t()
  example rewritten_fibonacci(n \\ 8) do
    {:ok, rewritten, _trace} =
      Pipeline.run(doubling(), %Statement{rels: [EUser.fib()], args: [n]})

    {:ok, statement} = Statement.opened(rewritten, [:r, :e])
    witness = Statement.witness(statement)

    assert claimed(statement) == EUser.fib(n)

    assert Semantics.valid?(Statement.pred(statement), witness)

    statement
  end

  @doc "I am fibonacci reduced at every step: the source that says what it reduces by."
  @spec fibm_rel(pos_integer()) :: Rel.t()
  def fibm_rel(m \\ @mod) do
    Zkfol.Lang.rel :fibm do
      fibm(1, 1)
      fibm(2, 1)

      fibm(x, v) do
        x > 2
        fibm(x - 1, v1)
        fibm(x - 2, v2)
        v = mod(v1 + v2, ^m)
      end
    end
  end

  @spec rewritten_fibonacci_mod(pos_integer(), pos_integer()) :: Statement.t()
  example rewritten_fibonacci_mod(n \\ 1_000, mod \\ @mod) do
    {:ok, rewritten, _trace} =
      Pipeline.run(doubling(), %Statement{rels: [fibm_rel(mod)], args: [n]})

    {:ok, statement} = Statement.opened(rewritten, [:r, :e])
    witness = Statement.witness(statement)

    assert claimed(statement) == fib_mod(n, mod)

    assert Semantics.valid?(Statement.pred(statement), witness)

    statement
  end

  @spec one_predicate_for_every_n() :: Ast.pred()
  example one_predicate_for_every_n do
    small = rewritten_fibonacci(100)
    large = rewritten_fibonacci(10_000)

    assert Statement.pred(small) == Statement.pred(large)
    assert Interpretation.len(Statement.witness(small)) == 7
    assert Interpretation.len(Statement.witness(large)) == 14
    Statement.pred(small)
  end

  @doc "Fibonacci finds a missing input, accepts its answer, and refuses another."
  @spec fibonacci_questions() :: Statement.t()
  example fibonacci_questions do
    for n <- [1, 2, 8] do
      answer = EUser.fib(n)
      source = Statement.of(EUser.fib(), args: [n, answer])
      assert {:ok, rewritten, _} = Pipeline.run(Pipeline.default(), source)
      assert Semantics.valid?(Statement.pred(rewritten), Statement.witness(rewritten))

      assert {:error, _pass, {:no_answer, _}, _} =
               Pipeline.run(Pipeline.default(), %{source | args: [n, answer + 1]})
    end

    {:ok, statement, _trace} =
      Pipeline.run(Pipeline.default(), Statement.of(EUser.fib(), args: [:_, 21]))

    witness = Statement.witness(statement)
    assert Interpretation.len(witness) == 8
    assert Interpretation.at(witness, 1, 8) == 21
    statement
  end

  @doc "Guards, shared variables and modular quotients keep the same answer with or without rewriting."
  @spec constrained_recurrences() :: [Statement.t()]
  example constrained_recurrences do
    guarded =
      Zkfol.Lang.rel :guarded do
        guarded(1, 1)
        guarded(2, 1)

        guarded(n, v) do
          n > 10
          guarded(n - 1, a)
          guarded(n - 2, b)
          v = a + b
        end
      end

    constrained =
      Zkfol.Lang.rel :constrained do
        constrained(1, 1)
        constrained(2, 1)

        constrained(n, v) do
          n > 2
          v = 999
          constrained(n - 1, a)
          constrained(n - 2, b)
          v = a + b
        end
      end

    shared =
      Zkfol.Lang.rel :shared do
        shared(1, 1)
        shared(2, 1)

        shared(n, v) do
          n > 2
          shared(n - 1, a)
          shared(n - 2, a)
          v = a + a
        end
      end

    difference =
      Zkfol.Lang.rel :difference do
        difference(1, 0)
        difference(2, 2)

        difference(n, r) do
          n > 2
          difference(n - 1, a)
          difference(n - 2, b)
          r = mod(a - b, 2)
        end
      end

    for rel <- [guarded, constrained, shared, difference] do
      source = Statement.of(rel, args: [4])
      assert Doubling.run(source, []) == {:ok, source}
      assert {:error, _pass, {:no_answer, _}, _} = Pipeline.run(EUser.plain(), source)
      assert {:error, _pass, {:no_answer, _}, _} = Pipeline.run(Pipeline.default(), source)
      source
    end
  end

  @doc "An optimizer declines custom meanings on the root, a helper or a helper's callee."
  @spec recurrence_meanings() :: [Statement.t()]
  example recurrence_meanings do
    fib = EUser.fib()
    zero = Zkfol.Lang.rel(:natural, do: natural(0))
    denied = "> 1 2"

    for rels <- [
          [%{fib | al: denied}],
          [fib, %{Zkfol.Prims.gt() | al: denied}],
          [fib, zero]
        ] do
      source = Statement.of(rels, args: [8, 21])
      assert Doubling.run(source, []) == {:ok, source}
      source
    end
  end

  @spec doubling() :: Pipeline.t()
  defp doubling, do: %Pipeline{passes: [{Doubling, []}]}

  @doc "I am the comparator loop: the recurrence stepped n times, reduced at every step."
  @spec fib_mod(pos_integer(), pos_integer()) :: non_neg_integer()
  def fib_mod(n, mod \\ @mod) do
    {value, _next} = Enum.reduce(1..n, {0, 1}, fn _, {a, b} -> {b, rem(a + b, mod)} end)
    value
  end

  @doc "I read the claimed result out of a rewritten statement's witness: the head claim."
  @spec claimed(Statement.t()) :: integer()
  def claimed(statement = %Statement{}) do
    [{_name, row, column} | _rest] = Statement.claims(statement)
    Interpretation.at(Statement.witness(statement), row, column)
  end
end
