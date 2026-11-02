defmodule Zkfol.Backend do
  @moduledoc "I lower and prove a predicate on its witness."

  alias Zkfol.Ast
  alias Zkfol.Interpretation
  alias Zkfol.Prover.Report
  alias Zkfol.Refusal

  @doc "I lower `pred` for my backend and prove it on `witness`."
  @callback prove(Ast.pred(), Interpretation.t(), keyword()) ::
              {:ok, Report.t(), pos_integer()} | {:error, Refusal.t()}
end
