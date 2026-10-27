defmodule Zkfol.Query do
  @moduledoc """
  I own the heap-capped process that enumerates an AL query's answers.

  ### Public API

  - `open/3`: install the program and start its query process.
  - `next/1`: the next answer, the end of the search, or a refusal.
  - `taken/1`: every answer handed out so far, oldest first.
  - `statement/2`: answer `k` as a statement, ready to prove.
  - `close/1`: stop the process and retract the installed methods.
  """

  use GenServer
  use TypedStruct

  alias Zkfol.Al
  alias Zkfol.Lang.Rel
  alias Zkfol.Statement
  alias Zkfol.Refusal

  @type answer :: [Statement.datum()]
  @type outcome :: {:ok, answer()} | :exhausted | {:error, Refusal.t()}

  @typedoc "The query process and its installed program, retained for cleanup."
  typedstruct enforce: true do
    field(:pid, pid())
    field(:program, AL.Object.t())
  end

  ############################################################
  #                        Public API                        #
  ############################################################

  @doc "I open a query at `arguments`, `:_` free; `opts` takes `:heap` and `:branch`."
  @spec open(Statement.t() | Rel.t() | [Rel.t()], [Zkfol.Statement.datum() | :_], keyword()) ::
          {:ok, t()} | {:error, Refusal.t()}
  def open(rels, arguments, opts) do
    with {:ok, program, source} <- Al.install(rels, arguments, opts),
         {:ok, pid} <- GenServer.start(__MODULE__, {program, source, opts}) do
      {:ok, %__MODULE__{pid: pid, program: program}}
    end
  end

  @doc "I am the query's next answer, `:exhausted`, or the refusal that stopped it."
  @spec next(t()) :: outcome()
  def next(query = %__MODULE__{pid: pid}) do
    GenServer.call(pid, :next, :infinity)
  catch
    :exit, _killed ->
      close(query)
      {:error, {:heap_exhausted, %{said: "the query exceeded its heap"}}}
  end

  @doc "I am every answer this query has handed out, oldest first."
  @spec taken(t()) :: [answer()]
  def taken(%__MODULE__{pid: pid}) do
    GenServer.call(pid, :taken, :infinity)
  catch
    :exit, _gone -> []
  end

  @doc "I return answer `k` (the latest by default) as a statement, or nil if search ends first."
  @spec statement(t(), pos_integer() | :latest) :: Statement.t() | nil
  def statement(query, k \\ :latest)

  def statement(%__MODULE__{pid: pid}, k) do
    GenServer.call(pid, {:statement, k}, :infinity)
  catch
    :exit, _gone -> nil
  end

  @doc "I stop the query and retract its installed methods, however it ended."
  @spec close(t()) :: :ok | {:error, Refusal.t()}
  def close(%__MODULE__{pid: pid, program: program}) do
    GenServer.stop(pid)
  catch
    :exit, _gone -> Al.close(program)
  end

  ############################################################
  #                    GenServer Callbacks                   #
  ############################################################

  @impl true
  def init({program, source, opts}) do
    Process.flag(:trap_exit, true)

    Process.flag(:max_heap_size, %{
      size: Keyword.get(opts, :heap) || 256_000_000,
      kill: true,
      error_logger: false
    })

    {:ok, {program, source, nil, []}}
  end

  @impl true
  def handle_call(:next, _from, query) do
    {outcome, query} = advance(query)
    {:reply, outcome, query}
  end

  def handle_call(:taken, _from, query = {_, _, _, taken}),
    do: {:reply, Enum.reverse(taken), query}

  def handle_call({:statement, k}, _from, query) do
    {_, source, _, taken} = query = advance_to(query, k)
    answer = if k == :latest, do: List.first(taken), else: Enum.at(Enum.reverse(taken), k - 1)
    {:reply, answer && %{source | args: answer}, query}
  end

  @impl true
  def terminate(_reason, {program, _, _, _}), do: Al.close(program)

  ############################################################
  #                   Private Implementation                 #
  ############################################################

  defp advance(query = {program, source, continuation, taken}) do
    result =
      case continuation do
        nil -> Al.invoke(program, source)
        state -> state |> AL.next_solution() |> Al.result()
      end

    case result do
      {:ok, state} ->
        [%AL.Goal.Compound{args: [_object | args]}] = state.program
        answer = AL.Var.subst(args, state.active_choicepoint.store)
        query = {program, source, state, taken}

        if ground?(answer),
          do: {{:ok, answer}, {program, source, state, [answer | taken]}},
          else: {{:error, {:residue, %{answer: answer}}}, query}

      {:no, _} ->
        {:exhausted, query}

      {:error, _} = refusal ->
        {refusal, query}
    end
  end

  defp advance_to(query = {_, _, _, taken}, k) when k == :latest or length(taken) >= k,
    do: query

  defp advance_to(query, k) do
    case advance(query) do
      {{:ok, _}, query} -> advance_to(query, k)
      {_, query} -> query
    end
  end

  defp ground?([]), do: true
  defp ground?([head | tail]), do: ground?(head) and ground?(tail)
  defp ground?(value), do: is_integer(value)
end
