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

  @doc "A truncated exported proof must fail verification while the original remains valid."
  @spec truncated_proof_is_rejected() :: :ok
  example truncated_proof_is_rejected do
    prefix =
      Path.join(System.tmp_dir!(), "zkfol-proof-integrity-#{System.unique_integer([:positive])}")

    original = prefix <> ".proof"
    truncated = prefix <> ".truncated.proof"
    statement = prefix <> ".json"
    binary = Application.app_dir(:zkfol, "priv/native/zkfol_verify")

    try do
      ran = Zkfol.compile(%Statement{rels: [EUser.fib()], args: [8]}, public: [:r], export: prefix)
      assert %Prover.Report{} = Log.report(Log.snapshot(), ran)

      assert {_output, 0} = System.cmd(binary, [statement, original], stderr_to_stdout: true)

      bytes = File.read!(original)
      assert byte_size(bytes) > 1
      :ok = File.write(truncated, binary_part(bytes, 0, byte_size(bytes) - 1))

      assert {_output, status} =
               System.cmd(binary, [statement, truncated], stderr_to_stdout: true)

      assert status != 0
      assert {_output, 0} = System.cmd(binary, [statement, original], stderr_to_stdout: true)
      :ok
    after
      for path <- [original, truncated, statement], do: File.rm(path)
    end
  end

end
