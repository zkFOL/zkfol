defmodule Zkfol.Prover do
  @moduledoc """
  I am the one actor the NIF answers to, journaling each intent and the verdict that
  settles it on the log.
  """

  use GenServer
  use EventBroker.DefFilter
  use TypedStruct

  alias Zkfol.Ast
  alias Zkfol.Interpretation
  alias Zkfol.Log
  alias Zkfol.Refusal
  alias Zkfol.Uair
  alias Zkfol.ZincPlus

  deffilter Settled, intent: pos_integer() do
    %EventBroker.Event{body: %Zkfol.Log.Event{basedon: ^intent}} -> true
    _ -> false
  end

  typedstruct module: Report, enforce: true do
    @moduledoc """
    I am the verdict as a value: the NIF's measurements and the claims read in the clear.
    I exist only where the proof verified.
    """

    field(:prove_ms, float())
    field(:verify_ms, float())
    field(:num_vars, non_neg_integer())
    field(:public_cols, non_neg_integer())
    field(:proof_bytes, non_neg_integer())
    field(:backend, String.t())
    field(:claims, [{String.t(), non_neg_integer()}])
  end

  @spec start_link(term()) :: GenServer.on_start()
  def start_link(_opts), do: GenServer.start_link(__MODULE__, %{}, name: __MODULE__)

  @doc "I emit and prove `pred` on `witness`; `opts` takes `:name`, `:basedon`, `:claims`."
  @spec prove(Ast.pred(), Interpretation.t(), keyword()) ::
          {:ok, Report.t(), pos_integer()} | {:error, Refusal.t()}
  def prove(pred, witness, opts \\ []) do
    with {:ok, uair} <- Uair.emit(pred, witness, Keyword.get(opts, :claims, [])) do
      prove_uair(uair, opts)
    end
  end

  @doc "I prove `uair` through the log; `opts` takes `:name`, `:basedon`, `:timeout`, and the transport's own."
  @spec prove_uair(Uair.t(), keyword()) ::
          {:ok, Report.t(), pos_integer()} | {:error, Refusal.t()}
  def prove_uair(uair, opts \\ []) do
    id = Log.push({:prove_requested, Keyword.get(opts, :name)}, Keyword.get(opts, :basedon))
    filter = [%Settled{intent: id}]
    EventBroker.subscribe_me(filter)

    try do
      with :ok <- run(uair, id, opts),
           do: settled(id, Keyword.get(opts, :timeout, 60_000))
    after
      EventBroker.unsubscribe_me(filter)
      drained(id)
    end
  end

  # Only this intent's verdict, so one lingering from an abandoned wait is never heard here.
  @spec settled(pos_integer(), timeout()) ::
          {:ok, Report.t(), pos_integer()} | {:error, Refusal.t()}
  defp settled(id, timeout) do
    receive do
      %EventBroker.Event{body: %Log.Event{basedon: ^id, body: {:proved, report}}} ->
        {:ok, report, id}

      %EventBroker.Event{body: %Log.Event{basedon: ^id, body: {:prove_failed, reason}}} ->
        {:error, reason}
    after
      timeout -> {:error, {:prover_timeout, %{intent: id}}}
    end
  end

  @spec drained(pos_integer()) :: :ok
  defp drained(id) do
    receive do
      %EventBroker.Event{body: %Log.Event{basedon: ^id}} -> drained(id)
    after
      0 -> :ok
    end
  end

  @spec run(Uair.t(), pos_integer(), keyword()) :: :ok | {:error, Refusal.t()}
  defp run(uair, intent, opts), do: GenServer.call(__MODULE__, {:run, uair, intent, opts})

  @impl true
  def init(inflight) do
    # Trap exits so terminate/2 settles the verdicts owed at death.
    Process.flag(:trap_exit, true)
    {:ok, inflight}
  end

  @impl true
  def handle_call({:run, uair, intent, opts}, _from, inflight) do
    with {:ok, claims} <- Uair.claimed(uair),
         {:ok, req} <- ZincPlus.request(uair, opts) do
      {:reply, :ok, Map.put(inflight, req, {intent, claims})}
    else
      {:error, reason} = error ->
        Log.push({:prove_failed, reason}, intent)
        {:reply, error, inflight}
    end
  end

  @impl true
  def handle_info({:zinc_plus, req, result}, inflight) do
    case Map.pop(inflight, req) do
      {nil, inflight} ->
        {:noreply, inflight}

      {{intent, claims}, inflight} ->
        case result do
          {:ok, report} ->
            Log.push({:proved, struct!(Report, Map.put(report, :claims, claims))}, intent)

          {:error, reason} ->
            Log.push({:prove_failed, Refusal.from_backend(reason)}, intent)
        end

        {:noreply, inflight}
    end
  end

  @impl true
  def terminate(_reason, inflight) do
    for {_req, {intent, _claims}} <- inflight do
      Log.push({:prove_failed, {:prover_died, %{}}}, intent)
    end
  end
end
