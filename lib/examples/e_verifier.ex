defmodule Examples.EVerifier do
  @moduledoc """
  I am the standalone verifier's evidence: a proof leaves the prover as two files, and a
  separate process accepts it, or rejects each way it can be spoiled.
  """

  use ExExample

  import ExUnit.Assertions

  alias Examples.EUser
  alias Zkfol.Log
  alias Zkfol.Prover
  alias Zkfol.Refusal
  alias Zkfol.Statement
  alias Zkfol.Uair
  alias Zkfol.Verifier
  alias Zkfol.Verifier.Accepted
  alias Zkfol.Verifier.Request

  @doc "Examples write real files and the verifier is a real process, so each run is fresh."
  @spec rerun?(term()) :: boolean()
  def rerun?(_example), do: true

  @doc "I prove fibonacci 8 with its result public, and keep the proof as two files."
  @spec exported() :: Request.t()
  example exported do
    prefix = fresh_prefix("fibonacci")
    source = %Statement{rels: [EUser.fib()], args: [8]}
    ran = Zkfol.compile(source, name: :fibonacci, public: [:r], export: prefix)
    assert %Prover.Report{} = Log.report(Log.snapshot(), ran)

    request = %Request{proof: prefix <> ".proof", public: prefix <> ".public.json"}
    assert File.exists?(request.proof)
    assert File.exists?(request.public)
    request
  end

  @doc "A process that was given only the two files accepts the proof."
  @spec accepted() :: Accepted.t()
  example accepted do
    assert {:ok, %Accepted{} = accepted} = Verifier.verify(exported())
    accepted
  end

  @doc """
  The public file holds the public columns and no others: the witness never reaches it.
  """
  @spec public_inputs_hold_only_public_columns() :: map()
  example public_inputs_hold_only_public_columns do
    %{"num_vars" => num_vars, "spec" => spec, "public" => %{"I64" => columns}} =
      exported().public |> File.read!() |> JSON.decode!()

    assert spec["num_cols"] > spec["num_public"]
    assert length(columns) == spec["num_public"]
    assert Enum.all?(columns, &(length(&1) == 2 ** num_vars))
    spec
  end

  @doc "A single flipped bit anywhere in the proof is a rejection."
  @spec flipped_proof_rejected() :: Refusal.t()
  example flipped_proof_rejected do
    request = exported()
    bytes = File.read!(request.proof)

    refusals =
      for at <- [0, div(byte_size(bytes), 2), byte_size(bytes) - 1] do
        <<head::binary-size(at), byte, tail::binary>> = bytes
        spoiled = <<head::binary, Bitwise.bxor(byte, 1), tail::binary>>
        refused(request, &File.write!(&1.proof, spoiled))
      end

    assert {:ok, %Accepted{}} = Verifier.verify(request)
    List.last(refusals)
  end

  @doc "A proof cut short, extended, or replaced by noise is a rejection and not a crash."
  @spec malformed_proof_rejected() :: Refusal.t()
  example malformed_proof_rejected do
    request = exported()
    bytes = File.read!(request.proof)
    noise = :crypto.strong_rand_bytes(byte_size(bytes))
    malformed = ["", "noise", binary_part(bytes, 0, byte_size(bytes) - 1), bytes <> <<0>>, noise]

    malformed
    |> Enum.map(fn bad -> refused(request, &File.write!(&1.proof, bad)) end)
    |> List.last()
  end

  @doc "The proof is bound to its public inputs: change one cell and it is a rejection."
  @spec edited_public_input_rejected() :: Refusal.t()
  example edited_public_input_rejected do
    request = exported()

    refused(request, fn %Request{public: path} ->
      edited =
        path
        |> File.read!()
        |> JSON.decode!()
        |> update_in(["public", "I64", Access.at(0), Access.at(0)], &(&1 + 1))

      File.write!(path, JSON.encode!(edited))
    end)
  end

  @doc """
  A false statement is not proved: the prover is run on a spoiled witness and writes
  nothing, so there is no proof file for a verifier to be shown.
  """
  @spec false_statement_leaves_no_proof() :: Refusal.t()
  example false_statement_leaves_no_proof do
    prefix = fresh_prefix("forged")
    {:ok, statement, _trace} = Zkfol.Pipeline.run(EUser.plain(), fib_statement())
    {:ok, uair} = Uair.emit(Statement.pred(statement), Statement.witness(statement))
    last = Uair.num_cols(uair) - 1
    forged = List.update_at(uair.columns, last, &List.update_at(&1, 3, fn cell -> cell + 1 end))

    assert {:error, refusal = {:verifier_rejected, _}} =
             Prover.prove_uair(%{uair | columns: forged}, export: prefix)

    refute File.exists?(prefix <> ".proof")
    refute File.exists?(prefix <> ".public.json")
    refusal
  end

  @spec fib_statement() :: Statement.t()
  defp fib_statement, do: %Statement{rels: [EUser.fib()], args: [8]}

  # I spoil a copy of the request with `spoil`, return the verifier's refusal, and leave
  # the original files as I found them.
  @spec refused(Request.t(), (Request.t() -> term())) :: Refusal.t()
  defp refused(%Request{} = request, spoil) do
    saved = {File.read!(request.proof), File.read!(request.public)}
    spoil.(request)
    assert {:error, refusal = {:verifier_rejected, _}} = Verifier.verify(request)
    File.write!(request.proof, elem(saved, 0))
    File.write!(request.public, elem(saved, 1))
    refusal
  end

  @spec fresh_prefix(String.t()) :: Path.t()
  defp fresh_prefix(name) do
    dir = Path.join(System.tmp_dir!(), "zkfol-verifier-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    Path.join(dir, name)
  end
end
