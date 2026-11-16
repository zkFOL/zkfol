defmodule Examples.EBench do
  @moduledoc """
  I am the zkFOL column of the zkvm-fib-bench tables: one example per row, `report/0` the
  whole column. I join the suite only under `BENCH=1`.
  """

  use ExExample
  use Zkfol

  alias Examples.EAl
  alias Examples.EDoubling
  alias Examples.ESudoku
  alias Examples.EUser
  alias Zkfol.Pipeline
  alias Zkfol.Prover
  alias Zkfol.Query
  alias Zkfol.Statement
  alias Zkfol.Uair

  defrel bounded(x) do
    x > 9
    x < 101
  end

  @doc "Section 1: fib(n) mod 7919, the naive recurrence rewritten to doubling."
  @spec doubled_fibonacci_mod(pos_integer(), pos_integer()) :: map()
  example doubled_fibonacci_mod(n \\ 10_000, mod \\ 7919) do
    measurement("fibonacci n=#{n} mod #{mod}, doubled", EDoubling.rewritten_fibonacci_mod(n, mod))
  end

  @doc "Sections 1 and 3: exact fib(n), the naive recurrence rewritten to doubling."
  @spec doubled_fibonacci(pos_integer()) :: map()
  example doubled_fibonacci(n \\ 10_000) do
    measurement("fibonacci n=#{n}, doubled", EDoubling.rewritten_fibonacci(n))
  end

  @doc "Section 2: the floor, 10 <= x <= 100 and nothing else."
  @spec bounds_check(pos_integer()) :: map()
  example bounds_check(x \\ 42) do
    measurement("bounded x=#{x}", solved(bounded(), [x]))
  end

  @doc "Section 3: fib(n) mod 7919 by the linear loop, the zkbenchmarks program as a relation."
  @spec registers_fibonacci_mod(pos_integer()) :: map()
  example registers_fibonacci_mod(n \\ 10_000) do
    measurement("fibonacci n=#{n}, registers mod 7919", solved(EAl.regsm(), [n, :_, :_]))
  end

  @doc "The reproduce table: exact fib(n) by the linear loop."
  @spec registers_fibonacci(pos_integer()) :: map()
  example registers_fibonacci(n \\ 10_000) do
    measurement("fibonacci n=#{n}, registers", solved(EUser.regs(), [n]))
  end

  @doc "Section 4: the 9x9 grid stands under its clues; nothing of the grid is public."
  @spec sudoku() :: map()
  example sudoku do
    measurement("sudoku 9x9", solved(ESudoku.solved(), ESudoku.act()))
  end

  @doc "Section 4: the 16x16 grid, through the same sudoku/2 as the 9x9, range checks included."
  @spec sudoku16() :: map()
  example sudoku16 do
    measurement(
      "sudoku 16x16",
      solved(ESudoku.solved16(), ESudoku.act16())
    )
  end

  @doc "Section 4, solving not only checking: the 9x9 answered from its seventeen clues."
  @spec sudoku_solve() :: map()
  example sudoku_solve do
    {us, query} = :timer.tc(fn -> Zkfol.eval!(ESudoku.solved(), [:_], heap: 32_000_000) end)
    Query.close(query)
    %{statement: "sudoku 9x9 solve", solve_ms: us / 1_000}
  end

  @doc "I am the zkFOL column, in the tables' order."
  @spec report() :: [map()]
  example report do
    [
      doubled_fibonacci_mod(),
      doubled_fibonacci(),
      bounds_check(),
      registers_fibonacci_mod(),
      registers_fibonacci(),
      sudoku(),
      sudoku16(),
      sudoku_solve()
    ]
  end

  @doc "I prove a solved statement and keep the numbers; the rss peak resets at entry."
  @spec measurement(String.t(), Statement.t()) :: map()
  def measurement(name, statement) do
    rss_baseline_mb = reset_peak_rss()

    {:ok, uair} =
      Uair.emit(
        Statement.pred(statement),
        Statement.witness(statement),
        Statement.claims(statement)
      )

    {:ok, report, _id} = Prover.prove_uair(uair, name: name, timeout: :infinity)

    %{
      statement: name,
      backend: report.backend,
      prove_ms: report.prove_ms,
      verify_ms: report.verify_ms,
      proof_bytes: report.proof_bytes,
      program: length(uair.program),
      rss_baseline_mb: rss_baseline_mb,
      rss_peak_mb: peak_mb(:os.type())
    }
  end

  @spec solved(Zkfol.Lang.Rel.t(), [Statement.datum() | :_]) :: Statement.t()
  defp solved(rel, args) do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [rel], args: args})

    statement
  end

  @spec reset_peak_rss() :: non_neg_integer()
  defp reset_peak_rss do
    Enum.each(Process.list(), &:erlang.garbage_collect/1)
    with {:unix, :linux} <- :os.type(), do: File.write!("/proc/self/clear_refs", "5")
    rss_mb(:os.type())
  end

  @typep host() :: {:unix | :win32, atom()}

  @spec rss_mb(host()) :: non_neg_integer()
  defp rss_mb({:unix, :linux}), do: div(proc_status("VmRSS:"), 1024)

  defp rss_mb({:unix, _os}) do
    {rss, 0} = System.cmd("ps", ["-o", "rss=", "-p", System.pid()])
    rss |> String.trim() |> String.to_integer() |> div(1024)
  end

  @spec peak_mb(host()) :: non_neg_integer()
  defp peak_mb({:unix, :linux}), do: div(proc_status("VmHWM:"), 1024)
  defp peak_mb(host), do: rss_mb(host)

  @spec proc_status(String.t()) :: non_neg_integer()
  defp proc_status(key) do
    "/proc/self/status"
    |> File.read!()
    |> String.split("\n")
    |> Enum.find(&String.starts_with?(&1, key))
    |> String.split()
    |> Enum.at(1)
    |> String.to_integer()
  end
end
