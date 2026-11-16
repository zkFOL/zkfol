defmodule Examples.EFacts do
  @moduledoc "I am the facts' evidence: the descriptor read off the clauses, or the refusal."

  use ExExample
  use Zkfol
  import ExUnit.Assertions

  alias Examples.EUser
  alias Zkfol.Facts
  alias Zkfol.Refusal

  defrel factorial(1, 1)
  defrel factorial(2, 2)

  defrel factorial(x, v) do
    x > 2
    x1 = x - 1
    factorial(x1, v1)
    v = x * v1
  end

  defrel reduced(1, 1)
  defrel reduced(2, 1)

  defrel reduced(x, v) do
    x1 = x - 1
    reduced(x1, a)
    x2 = x - 2
    reduced(x2, b)
    mod(a + b, 1000, v)
  end

  defrel entangled(1, 1)
  defrel entangled(2, 1)

  defrel entangled(x, v) do
    x1 = x - 1
    entangled(x1, a)
    x2 = x - 2
    entangled(x2, b)
    v = a * b
  end

  @spec recurrences() :: [Facts.t()]
  example recurrences do
    {:ok, reduced} = Facts.of(reduced())
    {:ok, fib} = Facts.of(EUser.fib())

    assert reduced == %Facts{base: [{1, 1}, {2, 1}], coefficients: {1, 1}, modulus: 1000}
    assert fib == %{reduced | modulus: nil}
    [reduced, fib]
  end

  @spec refusals() :: [Refusal.t()]
  example refusals do
    for rel <- [factorial(), entangled(), EUser.regs()] do
      assert {:error, {:not_a_recurrence, %{relation: _}} = refusal} = Facts.of(rel)
      refusal
    end
  end
end
