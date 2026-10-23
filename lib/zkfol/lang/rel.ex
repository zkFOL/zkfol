defmodule Zkfol.Lang.Rel do
  @moduledoc "I am a named relation: clauses of one head shape."

  alias Zkfol.Lang.Term
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

  @doc "I am the calls that need named relations; names also used as values may be callbacks."
  @spec calls(t()) :: [Term.name()]
  def calls(%__MODULE__{clauses: clauses}),
    do:
      for(
        {head, body} <- clauses,
        bound = MapSet.new(Term.names(head ++ body)),
        {:call, q, _args} <- body,
        not match?({:var, _}, q) and not (is_atom(q) and MapSet.member?(bound, q)),
        uniq: true,
        do: q
      )

  @doc "I am the relations my clauses mention as values, including inside equations and structures."
  @spec passes(t()) :: [Term.name()]
  def passes(%__MODULE__{clauses: clauses}),
    do:
      for(
        {head, body} <- clauses,
        bound = MapSet.new(Term.names(head)),
        name <-
          Term.reduce(body, [], fn
            {tag, name, args}, names when tag in [:call, :papply] ->
              bare = for {:var, v} <- args, v not in bound, do: v
              passed = if tag == :papply, do: [name | bare], else: bare
              Enum.reverse(passed, names)

            _term, names ->
              names
          end)
          |> Enum.reverse(),
        uniq: true,
        do: name
      )
end
