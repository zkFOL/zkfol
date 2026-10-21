defmodule Zkfol.Pipeline do
  @moduledoc """
  I am a pipeline as a value: a list of `{module, opts}` passes, each
  taking a statement to the next or refusing with the reason.
  """

  use TypedStruct

  alias Zkfol.Doubling
  alias Zkfol.Refusal
  alias Zkfol.Statement
  alias Zkfol.Witness

  @doc "I take `statement` to the next statement, or refuse with the reason."
  @callback run(Statement.t(), keyword()) :: {:ok, Statement.t()} | {:error, Refusal.t()}

  @doc "I am the verb of my act: what a run of mine that changed the statement did."
  @callback verb() :: result()

  @typedoc "One member: the pass module and its options."
  @type pass :: {module(), keyword()}

  @typedoc "Each pass and the statement it produced, in order."
  @type trace :: [{module(), Statement.t()}]

  @typedoc "What a run came to: the final statement or the erring pass, the trace either way."
  @type outcome ::
          {:ok, Statement.t(), trace()} | {:error, module(), Refusal.t(), trace()}

  @type result :: :declines | :lowers | :rewrites | :solves | {:errors, Refusal.t()}

  typedstruct enforce: true do
    field(:passes, [pass()])
  end

  @doc "I am the default route: doubling, witness, lowering."
  @spec default() :: t()
  def default,
    do: %__MODULE__{passes: [{Doubling, []}, {Witness, []}, {Zkfol.Phi, []}]}

  @doc "I run `statement` through my passes, keeping every intermediate."
  @spec run(t(), Statement.t(), keyword()) :: outcome()
  def run(%__MODULE__{passes: passes}, statement, opts \\ []) do
    statement = %{statement | rels: program(statement.rels)}

    Enum.reduce_while(passes, {statement, []}, fn {pass, own}, {current, trace} ->
      case pass.run(current, Keyword.merge(opts, own)) do
        {:ok, next} -> {:cont, {next, [{pass, next} | trace]}}
        {:error, reason} -> {:halt, {:error, pass, reason, Enum.reverse(trace)}}
      end
    end)
    |> case do
      {:error, _pass, _reason, _trace} = refusal -> refusal
      {final, trace} -> {:ok, final, Enum.reverse(trace)}
    end
  end

  @spec program([Zkfol.Lang.Rel.t()]) :: [Zkfol.Lang.Rel.t()]
  defp program([root | _rest] = rels) do
    case Zkfol.Program.reached(root, rels) do
      {:ok, reached} -> reached
      {:error, _absent} -> rels
    end
  end

  defp program([]), do: []

  # Change the name
  @doc "I am the act's verdicts, one per pass, read off its trace."
  @spec verdicts(t(), Statement.t(), outcome()) :: [{module(), result()}]
  def verdicts(%__MODULE__{passes: passes}, statement, {:ok, _final, trace}),
    do: observed(passes, statement, trace)

  def verdicts(%__MODULE__{passes: passes}, statement, {:error, pass, reason, trace}),
    do: observed(passes, statement, trace) ++ [{pass, {:errors, reason}}]

  @spec observed([pass()], Statement.t(), trace()) :: [{module(), result()}]
  defp observed(passes, statement, trace) do
    stages = [statement | Enum.map(trace, &elem(&1, 1))]

    for {{pass, _opts}, [input, output]} <-
          Enum.zip(passes, Enum.chunk_every(stages, 2, 1, :discard)),
        do: {pass, if(output == input, do: :declines, else: pass.verb())}
  end
end
