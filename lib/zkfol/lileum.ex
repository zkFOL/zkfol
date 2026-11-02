defmodule Zkfol.Lileum do
  @moduledoc "I am the Lileum backend."

  @behaviour Zkfol.Backend

  use TypedStruct

  alias Zkfol.Ast
  alias Zkfol.Interpretation
  alias Zkfol.Lileum.Native
  alias Zkfol.Refusal

  @type expression ::
          {:var, non_neg_integer()}
          | {:add, expression(), expression()}
          | {:sub, expression(), expression()}
          | {:mul, expression(), expression()}

  @type cell :: {non_neg_integer(), non_neg_integer()}
  @type connection :: {cell(), cell()}

  typedstruct module: Structure, enforce: true do
    field(:columns, pos_integer())
    field(:arithmetic_constraints, [Zkfol.Lileum.expression()])
    field(:copy_constraints, [Zkfol.Lileum.connection()], default: [])
    field(:reads, [Zkfol.Lileum.connection()], default: [])
  end

  @doc "I lower local equations and conjunctions"
  @impl true
  @spec prove(Ast.pred(), Interpretation.t(), keyword()) :: {:error, Refusal.t()}
  def prove(pred, witness, opts) do
    structure = %Structure{
      columns: Interpretation.len(witness),
      arithmetic_constraints: constraints(pred)
    }

    columns =
      witness
      |> Interpretation.rows()
      |> Enum.zip_with(& &1)

    Native.prove(structure, columns, opts)
  end

  @spec constraints(Ast.pred()) :: [expression()]
  defp constraints({:eq, a, b}), do: [{:sub, expression(a), expression(b)}]
  defp constraints({:conj, preds}), do: Enum.flat_map(preds, &constraints/1)

  @spec expression(Ast.term_t()) :: expression()
  defp expression({:cell, i}) when is_integer(i) and i > 0, do: {:var, i - 1}
  defp expression({:add, a, b}), do: {:add, expression(a), expression(b)}
  defp expression({:mul, a, b}), do: {:mul, expression(a), expression(b)}
end
