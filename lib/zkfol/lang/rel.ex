defmodule Zkfol.Lang.Rel do
  @moduledoc """
  I am a named relation: clauses of one head shape.

  ### Public API

  - `name/1`: read a call target's name, leaving variable targets unchanged.
  """

  use TypedStruct

  typedstruct enforce: true do
    field(:name, atom())
    field(:arity, non_neg_integer())
    field(:clauses, [{[term()], [term()]}])
    # `phi` specializes lowering. `al` posts an additional constraint; a `:definition`
    # can also replace the clauses when asking for answers without a source derivation.
    field(:phi, {module(), atom()} | nil, default: nil, enforce: false)
    field(:al, Macro.t() | {:definition, Macro.t()} | nil, default: nil, enforce: false)
  end

  @doc "I read a constructor's relation name, or retain a self name or variable target."
  @spec name(Zkfol.Lang.Term.name() | {:var, atom()}) :: atom() | {:var, atom()}
  def name(ref) when is_function(ref, 0), do: ref.().name
  def name(name), do: name
end
