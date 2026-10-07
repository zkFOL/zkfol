defmodule Zkfol.ZincPlus.Native do
  @moduledoc """
  I am the NIF and nothing else, since a NIF module cannot be reloaded on a live node.
  """

  use Rustler, otp_app: :zkfol, crate: "zkfol_zinc_plus", mode: :release

  @doc "I hand the payload to the prover thread; the verdict arrives as a message."
  @spec prove_fol(term()) :: {:ok, pos_integer()} | {:error, String.t()}
  def prove_fol(_payload), do: :erlang.nif_error(:nif_not_loaded)

  @doc "I am the commitment a proof of the payload would carry to its witness, as hex."
  @spec commit_fol(term()) :: {:ok, String.t()} | {:error, String.t()}
  def commit_fol(_payload), do: :erlang.nif_error(:nif_not_loaded)

  @doc "I am the pinned code's parameters, read off the crate."
  @spec pcs_params() :: map()
  def pcs_params, do: :erlang.nif_error(:nif_not_loaded)
end
