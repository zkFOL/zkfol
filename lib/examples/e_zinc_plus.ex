defmodule Examples.EZincPlus do
  @moduledoc "I am the export's evidence: a process holding only the two files checks the proof."

  use ExExample

  import ExUnit.Assertions

  alias Examples.EUser
  alias Zkfol.Log
  alias Zkfol.Prover
  alias Zkfol.Statement

  @doc "I export fibonacci 8 being 21: `zkfol_verify` accepts it, and refuses it edited to 22."
  @spec exported() :: Path.t()
  example exported do
    prefix = Path.join(System.tmp_dir!(), "fibonacci")
    ran = Zkfol.compile(%Statement{rels: [EUser.fib()], args: [8]}, public: [:r], export: prefix)
    assert %Prover.Report{} = Log.report(Log.snapshot(), ran)

    binary = Application.app_dir(:zkfol, "priv/native/zkfol_verify")

    verify = fn statement ->
      System.cmd(binary, [statement, prefix <> ".proof"], stderr_to_stdout: true)
    end

    assert {_said, 0} = verify.(prefix <> ".json")

    edited = prefix <> ".22.json"

    (prefix <> ".json")
    |> File.read!()
    |> JSON.decode!()
    |> update_in(["public", "I64", Access.at(0), Access.at(0)], fn 21 -> 22 end)
    |> then(&File.write!(edited, JSON.encode!(&1)))

    assert {_said, 1} = verify.(edited)
    prefix
  end
end
