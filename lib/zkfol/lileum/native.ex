defmodule Zkfol.Lileum.Native do
  @moduledoc "I am the Lileum NIF boundary."

  use Rustler, otp_app: :zkfol, crate: "zkfol_lileum", mode: :release

  alias Zkfol.Lileum
  alias Zkfol.Refusal

  @doc "I am the pending native proof entry point."
  @spec prove(Lileum.Structure.t(), [[integer()]], keyword()) :: {:error, Refusal.t()}
  def prove(_structure, _columns, _opts),
    do: {:error, {:backend_unavailable, %{backend: Lileum}}}
end
