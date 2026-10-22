defmodule Zkfol.Al.Ask do
  @moduledoc """
  I am one stepping ask: the question installed on the branch I landed on, the
  goal that runs against it, the arguments the answer is shaped to, the heap a
  run of me may spend, and AL's search state between answers.
  """

  use TypedStruct

  @typedoc "One answer: the argument list ground, a cell an integer over N."
  @type answer :: [Zkfol.Statement.datum()]

  @typedoc "What one step of me yields: an answer, the end of the search, or a refusal."
  @type outcome :: {:ok, answer()} | :exhausted | {:error, Zkfol.Refusal.t()}

  typedstruct enforce: true do
    field(:rels, [Zkfol.Lang.Rel.t()])
    field(:goal, String.t())
    field(:arguments, [Zkfol.Statement.datum() | :_])
    field(:branch, AL.Branch.t())
    field(:class, atom())
    field(:heap, pos_integer())
    # My methods carry the trace size as a last argument, which a fact is not.
    field(:len?, boolean())
    field(:state, AL.JAM.State.t() | nil, default: nil)
  end
end
