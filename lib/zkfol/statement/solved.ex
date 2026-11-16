defmodule Zkfol.Statement.Solved do
  @moduledoc """
  I am the stage of a statement that has a linked predicate and the lay its witness
  is read off. My claims are the act's: only `Zkfol.Statement.opened/2` writes them.
  """

  use TypedStruct

  alias Zkfol.Ast
  alias Zkfol.Interpretation
  alias Zkfol.Lay

  typedstruct enforce: true do
    field(:pred, Ast.pred())
    field(:lay, Lay.t())
    field(:claims, [Interpretation.claim()], default: [], enforce: false)
    field(:lowering, [Zkfol.Phi.Clause.t()] | nil, default: nil, enforce: false)
  end
end
