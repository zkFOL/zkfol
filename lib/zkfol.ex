defmodule Zkfol do
  @moduledoc """
  I am the language's front door: one call takes a statement through a route to a proof,
  journalled, and returns the receipt.

  `use Zkfol` imports the relation macros and the FOL and primitive standard libraries.
  """

  alias Zkfol.Lang
  alias Zkfol.Log
  alias Zkfol.Pipeline
  alias Zkfol.Prover
  alias Zkfol.Query
  alias Zkfol.Refusal
  alias Zkfol.Statement
  alias Zkfol.Uair

  @typedoc "What a door takes: a statement, a root relation, or the relations in scope."
  @type target :: Statement.t() | Lang.Rel.t() | [Lang.Rel.t()]

  @doc "I bring the relational syntax and standard library into the caller's module."
  @spec __using__(keyword()) :: Macro.t()
  defmacro __using__(_opts) do
    quote do
      use Zkfol.Lang
      import Zkfol.FOL
      import Zkfol.Prims
    end
  end

  @doc "I am the whole act: define, run, verdicts, prove, receipt."
  @spec compile(target(), keyword()) :: Log.Run.t()
  def compile(target, opts \\ []), do: taken(target, opts, :compile)

  @doc "I am the act up to emit: define, run, verdicts, emit, a receipt with no proof."
  @spec emit(target(), keyword()) :: Log.Run.t()
  def emit(target, opts \\ []), do: taken(target, opts, :emit)

  @spec taken(target(), keyword(), Log.Args.entry()) :: Log.Run.t()
  defp taken(target, opts, entry) do
    {args, opts} = Keyword.pop(opts, :args, [])
    acted(Statement.of(target, args: args), opts, entry)
  end

  @doc """
  I am the query door: the relation run as AL runs it at `arguments`, `:_` free, the
  query holding its first answer; a binding nothing derives refuses.
  """
  @spec eval(Lang.Rel.t() | [Lang.Rel.t()] | Statement.t(), [Statement.datum() | :_], keyword()) ::
          {:ok, Query.t()} | {:error, Refusal.t()}
  def eval(rels, arguments, opts \\ []) do
    with {:ok, query} <- Query.open(rels, arguments, opts) do
      case Query.next(query) do
        {:ok, _answer} ->
          {:ok, query}

        :exhausted ->
          Query.close(query)
          {:error, {:no_answer, %{}}}

        {:error, reason} ->
          Query.close(query)
          {:error, reason}
      end
    end
  end

  @doc "I am `eval/3` for a hand at the keyboard: the query itself, a refusal raised."
  @spec eval!(Lang.Rel.t() | [Lang.Rel.t()] | Statement.t(), [Statement.datum() | :_], keyword()) ::
          Query.t()
  def eval!(rels, arguments, opts \\ []) do
    case eval(rels, arguments, opts) do
      {:ok, query} -> query
      {:error, reason} -> raise Refusal.message(reason)
    end
  end

  @doc """
  I am every answer at `arguments`, lazily, in the clauses' own order; a refusal ends the
  stream as exhaustion does.
  """
  @spec stream(Lang.Rel.t() | [Lang.Rel.t()], [Statement.datum() | :_], keyword()) ::
          Enumerable.t()
  def stream(rels, arguments, opts \\ []) do
    Stream.resource(
      fn -> Query.open(rels, arguments, opts) end,
      fn
        {:ok, query} = opened ->
          case Query.next(query) do
            {:ok, answer} -> {[answer], opened}
            _ended -> {:halt, opened}
          end

        {:error, _reason} = refusal ->
          {:halt, refusal}
      end,
      fn
        {:ok, query} -> Query.close(query)
        {:error, _reason} -> :ok
      end
    )
  end

  @spec acted(Statement.t(), keyword(), Log.Args.entry()) :: Log.Run.t()
  defp acted(statement, opts, entry) do
    {pipeline, opts} = Keyword.pop(opts, :pipeline, Pipeline.default())
    {name, opts} = Keyword.pop_lazy(opts, :name, fn -> named(statement) end)
    {public, opts} = Keyword.pop(opts, :public, [])
    args = %Log.Args{statement: statement, entry: entry, opts: opts}
    define = Log.push({:define, name, pipeline, public, args})

    outcome = Pipeline.run(pipeline, statement, basedon: define)
    piped = Log.push({:piped, Pipeline.verdicts(pipeline, statement, outcome)}, define)

    settled =
      with {:ok, final, _trace} <- outcome,
           {:ok, opened} <- Statement.opened(final, public),
           do: settle(entry, opened, Keyword.merge(opts, name: name, basedon: piped))

    with {:error, refusal} <- settled, do: Log.push({:refused, refusal}, piped)

    %Log.Run{defined: define}
  end

  @spec settle(Log.Args.entry(), Statement.t(), keyword()) ::
          {:ok, pos_integer() | nil} | {:error, Refusal.t()}
  # A route that stops short of the lowering leaves nothing to prove or emit.
  defp settle(_entry, %Statement{stage: stage}, _opts)
       when not is_struct(stage, Statement.Solved),
       do: {:error, {:not_solved, %{stage: staged(stage)}}}

  defp settle(:compile, final, opts), do: proved(final, opts)
  defp settle(:emit, final, opts), do: emitted(final, opts)

  @spec staged(Statement.stage()) :: atom()
  defp staged(:raw), do: :raw
  defp staged(%module{}), do: module

  @spec proved(Statement.t(), keyword()) :: {:ok, pos_integer()} | {:error, Refusal.t()}
  defp proved(final, opts) do
    prove = Keyword.put(opts, :claims, Statement.claims(final))

    with {:ok, _report, intent} <-
           Prover.prove(Statement.pred(final), Statement.witness(final), prove),
         do: {:ok, intent}
  end

  @spec emitted(Statement.t(), keyword()) :: {:ok, nil} | {:error, Refusal.t()}
  defp emitted(final, _opts) do
    with {:ok, _uair} <- Uair.emit(Statement.pred(final), Statement.witness(final)),
         do: {:ok, nil}
  end

  @spec named(Statement.t()) :: atom()
  defp named(%Statement{rels: [root | _rest]}), do: root.name
  defp named(_statement), do: :statement
end
