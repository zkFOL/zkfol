defmodule Zkfol.Phi.Schedule do
  @moduledoc """
  I run one worklist per member. Inlined bodies join that worklist, so their bindings
  are available to every waiting goal. Each item retains its original source context.

  A round runs ready goals in order and retains waits. If bindings changed, another
  round retries those waits. At a fixed point the caller may settle storage demands.

  ### Public API

  - `run/4`: run goals, expanding calls and retrying waits until bindings settle.
  """

  alias Zkfol.Phi.{Expression, Walk}

  defmodule Expansion do
    @moduledoc "I add an inlined body's scoped goals and head bindings to the current worklist."
    use TypedStruct

    typedstruct enforce: true do
      field(:goals, [term()])
      field(:walk, Walk.t())
    end
  end

  @type result :: Walk.t() | :dead | Expression.waiting() | Expansion.t()

  @doc "I run goals, preserving partial progress through inlined calls and deferred bindings."
  @spec run([term()], Walk.t(), (term(), Walk.t() -> result()), (Walk.t(),
                                                                 [Expression.dependency()] ->
                                                                   Walk.t() | Expression.waiting())) ::
          Walk.t() | :dead | Expression.waiting()
  def run(goals, walk, interpret, settle),
    do: resume(goals, [], walk.env, walk, interpret, settle)

  defp resume([], [], _before, walk, _interpret, _settle), do: walk

  defp resume([], blocked, before, walk, interpret, settle) do
    {goals, dependencies} = blocked |> Enum.reverse() |> Enum.unzip()
    names = dependencies |> List.flatten() |> Enum.uniq()
    more = if walk.env == before, do: settle.(walk, names), else: walk
    with %Walk{} <- more, do: run(goals, more, interpret, settle)
  end

  defp resume([goal | rest], blocked, before, walk, interpret, settle) do
    case interpret.(goal, walk) do
      :dead ->
        :dead

      {:waiting, names} ->
        resume(rest, [{goal, names} | blocked], before, walk, interpret, settle)

      %Expansion{goals: goals, walk: more} ->
        resume(goals ++ rest, blocked, before, more, interpret, settle)

      %Walk{} = more ->
        resume(rest, blocked, before, more, interpret, settle)
    end
  end
end
