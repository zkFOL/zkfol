defmodule Zkfol.Lang.Rel do
  @moduledoc "I am a named relation: clauses of one head shape."

  use TypedStruct

  typedstruct enforce: true do
    field(:name, atom())
    field(:arity, non_neg_integer())
    field(:clauses, [{[term()], [term()]}])
    field(:home, module() | nil, default: nil, enforce: false)
    # `phi` specializes lowering. `al` posts an additional constraint; a `:definition`
    # can also replace the clauses when asking for answers without a source derivation.
    field(:phi, {module(), atom()} | nil, default: nil, enforce: false)
    field(:al, Macro.t() | {:definition, Macro.t()} | nil, default: nil, enforce: false)
  end
end
