defmodule Zkfol.Verifier do
  @moduledoc """
  I verify a proof the way a stranger would: from a proof file and a public inputs file, in
  a separate OS process, and from nothing else.

  The boundary is the `Request` struct. It holds two paths and no term, so no plaintext can
  be handed across it, and the executable I run takes only those two paths. A malformed or
  tampered input is a rejection, never a crash.

  ### Public API

  - `verify/1` runs the standalone verifier on a request, and `pin/2` writes a pins file.
  - `executable/0` is the path of the verifier binary.
  """

  use TypedStruct

  alias Zkfol.Refusal

  typedstruct module: Request, enforce: true do
    @moduledoc """
    I am all a verifier is given: where the proof is, where its public inputs are, and
    optionally a pins file of values the proof must carry.
    """
    field(:proof, Path.t())
    field(:public, Path.t())
    field(:pins, Path.t() | nil, default: nil)
  end

  typedstruct module: Accepted, enforce: true do
    @moduledoc """
    I am a proof that verified: how long the verifier took, the proof's commitment to its
    witness, and the value of each binding, as hex.
    """
    field(:verify_ms, float())
    field(:commitment, String.t())
    field(:bindings, %{String.t() => String.t()})
  end

  @doc "I am the verifier binary, built by `mix compile` beside the NIF."
  @spec executable() :: Path.t()
  def executable, do: Application.app_dir(:zkfol, "priv/native/zkfol_verify")

  @doc """
  I run the verifier process on `request`. A proof it accepts is `{:ok, %Accepted{}}`;
  anything else, including a crash on malformed bytes, is `{:error, {:verifier_rejected, _}}`.
  """
  @spec verify(Request.t()) :: {:ok, Accepted.t()} | {:error, Refusal.t()}
  def verify(%Request{proof: proof, public: public, pins: pins}) do
    case System.cmd(executable(), [proof, public | List.wrap(pins)], stderr_to_stdout: true) do
      {out, 0} ->
        %{"verify_ms" => ms, "commitment" => commitment, "bindings" => bindings} = verdict(out)
        {:ok, %Accepted{verify_ms: ms, commitment: commitment, bindings: bindings}}

      {out, _status} ->
        {:error, {:verifier_rejected, %{said: said(out)}}}
    end
  end

  @doc "I write `pins`, expected values by binding name, where a verifier can read them."
  @spec pin(%{String.t() => String.t()}, Path.t()) :: Path.t()
  def pin(pins, path) do
    File.write!(path, JSON.encode!(pins))
    path
  end

  @spec verdict(String.t()) :: map()
  defp verdict(out) do
    case JSON.decode(out) do
      {:ok, verdict} -> verdict
      {:error, _} -> %{"reason" => String.trim(out)}
    end
  end

  @spec said(String.t()) :: String.t()
  defp said(out), do: Map.get(verdict(out), "reason", "verifier failed")
end
