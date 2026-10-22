defmodule Zkfol.ZincPlus.Native do
  @moduledoc """
  I am the NIF and nothing else, since a NIF module cannot be reloaded on a live node.
  """

  use Rustler, otp_app: :zkfol, crate: "zkfol_zinc_plus", mode: :release

  @doc "I hand the payload to the prover thread; the verdict arrives as a message."
  @spec prove_fol(
          Zkfol.Uair.t(),
          Zkfol.ZincPlus.cells(),
          pos_integer(),
          [Zkfol.ZincPlus.lookup()],
          [{non_neg_integer(), [non_neg_integer()], non_neg_integer()}],
          Path.t() | nil
        ) :: {:ok, pos_integer()} | {:error, String.t()}
  def prove_fol(_uair, _cells, _num_vars, _word_lookups, _reads, _export),
    do: :erlang.nif_error(:nif_not_loaded)

  @doc "I am the pinned code's parameters, read off the crate."
  @spec pcs_params() :: map()
  def pcs_params, do: :erlang.nif_error(:nif_not_loaded)
end
