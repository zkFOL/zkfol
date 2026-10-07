defmodule Zkfol.ZincPlus do
  @moduledoc """
  I am the Zinc+ backend behind a NIF: a UAIR goes in as a payload, the verdict comes back
  as `{:zinc_plus, id, result}`.
  """

  use TypedStruct

  import Bitwise

  alias Zkfol.Refusal
  alias Zkfol.Uair
  alias Zkfol.Uair.Composed
  alias Zkfol.Uair.Plain

  # One addition of headroom under each width the pinned backend offers.
  @i64_bound Integer.pow(2, 62)
  @big_bound Integer.pow(2, 766)
  @huge_bound Integer.pow(2, 7038)

  @typedoc "A word lookup: {column, table width, chunk width}."
  @type lookup :: {non_neg_integer(), pos_integer(), pos_integer()}

  typedstruct module: Selected, enforce: true do
    @typedoc """
    One Selected lookup group: the columns it spans, the multiset each claim holds, and the
    cells of each claim as `{slot, row}`. A cell no selection names is unconstrained.
    """
    field(:columns, [non_neg_integer()])
    field(:values, [non_neg_integer()])
    field(:selections, [[{non_neg_integer(), non_neg_integer()}]])
  end

  typedstruct module: Permuted, enforce: true do
    @typedoc """
    One Permuted lookup group: the columns it spans and its pairs of selections, each pair
    holding one multiset. Nothing prescribes the values.
    """
    field(:columns, [non_neg_integer()])

    field(
      :pairs,
      [{[{non_neg_integer(), non_neg_integer()}], [{non_neg_integer(), non_neg_integer()}]}]
    )
  end

  typedstruct module: Tie, enforce: true do
    @typedoc """
    One cell the statement fixes: its column, its row, and the column its private value
    fills at every row. Nothing of a tie is committed.
    """
    field(:column, non_neg_integer())
    field(:row, non_neg_integer())
    field(:target, {:broadcast, non_neg_integer()})
  end

  @typedoc "The trace columns tagged by the cell width they need."
  @type cells ::
          {:i64, [[integer()]]}
          | {:big, [[[non_neg_integer()]]]}
          | {:huge, [[[non_neg_integer()]]]}

  typedstruct module: Binding, enforce: true do
    @typedoc """
    A named value the statement binds: the public cells, as `{column, row}`, that hold it.
    The name is a label; the verifier reads the value from the cells.
    """
    field(:name, String.t())
    field(:cells, [{non_neg_integer(), non_neg_integer()}])
  end

  typedstruct module: Payload, enforce: true do
    @typedoc "One queued UAIR, as the NIF decodes it."
    field(:num_cols, pos_integer())
    field(:num_public, non_neg_integer())
    field(:shifts, [{non_neg_integer(), pos_integer()}])
    field(:program, [{atom(), integer()}])
    field(:cells, Zkfol.ZincPlus.cells())
    # A column declared here proves only if every cell is under 2^width.
    field(:word_lookups, [Zkfol.ZincPlus.lookup()], default: [])
    # A group proves only if every selection holds the multiset.
    field(:selected_lookups, [Zkfol.ZincPlus.Selected.t()], default: [])
    # A group proves only if each pair of selections holds one multiset.
    field(:permuted_lookups, [Zkfol.ZincPlus.Permuted.t()], default: [])
    field(:point_ties, [Zkfol.ZincPlus.Tie.t()], default: [])
    field(:reads, [{non_neg_integer(), [non_neg_integer()], non_neg_integer()}], default: [])
    field(:num_vars, pos_integer())
    # A path prefix: a proof that verifies is written to `<prefix>.proof` beside the public
    # inputs a verifier needs in `<prefix>.public.json`. Nothing private reaches either.
    field(:export, Path.t() | nil, default: nil)
    field(:bindings, [Zkfol.ZincPlus.Binding.t()], default: [])
  end

  @doc "I am the commitment a proof of `uair` would carry to its witness, without proving."
  @spec commit(Uair.t()) :: {:ok, String.t()} | {:error, Refusal.t()}
  def commit(uair = %Uair{}) do
    with {:ok, payload} <- payload(uair, []),
         {:ok, hex} <- Zkfol.ZincPlus.Native.commit_fol(payload) do
      {:ok, hex}
    else
      {:error, said} when is_binary(said) -> {:error, Refusal.from_backend(said)}
      {:error, refusal} -> {:error, refusal}
    end
  end

  @doc "I queue an interpreted UAIR on the prover thread."
  @spec prove_fol(Payload.t()) :: {:ok, pos_integer()} | {:error, String.t()}
  def prove_fol(payload), do: Zkfol.ZincPlus.Native.prove_fol(payload)

  @typedoc """
  The pinned code's parameters: a column encodes to `rep_factor` times its cells, an
  opening reveals `column_openings` positions, `degree` is the protocol's degree bound.
  """
  @type pcs_params :: %{
          rep_factor: pos_integer(),
          column_openings: pos_integer(),
          degree: pos_integer(),
          backend: String.t()
        }

  @doc "I answer the pinned code's parameters; they move with the dep."
  @spec pcs_params() :: pcs_params()
  def pcs_params, do: Zkfol.ZincPlus.Native.pcs_params()

  @doc """
  I queue the UAIR with the prover fitting its magnitude and return an id.

  `export: prefix` also writes the portable proof under `prefix` once it verifies; see
  `Zkfol.Verifier`.

  `unchecked: true` ships the payload as built, past `fits/1`. It is the door the
  negative tests need: a forgery the circuit must refuse cannot be watched being
  refused while Elixir refuses it first. No ordinary caller passes it.
  """
  @spec request(Uair.t(), keyword()) :: {:ok, pos_integer()} | {:error, Refusal.t()}
  def request(uair = %Uair{}, opts \\ []) do
    with {:ok, payload} <- payload(uair, opts),
         {:error, said} <- prove_fol(payload) do
      {:error, Refusal.from_backend(said)}
    end
  end

  @spec payload(Uair.t(), keyword()) :: {:ok, Payload.t()} | {:error, Refusal.t()}
  defp payload(uair, opts) do
    values = List.flatten(uair.columns)
    reads = reads(uair.mode)

    with :ok <- unclaimed(reads, uair.num_public),
         :ok <- if(Keyword.get(opts, :unchecked, false), do: :ok, else: fits(uair.columns)) do
      {:ok,
       %Payload{
         num_cols: Uair.num_cols(uair),
         num_public: uair.num_public,
         shifts: uair.shifts,
         program: Enum.map(uair.program, &wire/1),
         cells: cells(uair, values),
         word_lookups: uair.word_lookups,
         selected_lookups: uair.selected_lookups,
         permuted_lookups: uair.permuted_lookups,
         point_ties: uair.point_ties,
         reads: reads,
         num_vars: Uair.num_vars(uair),
         export: Keyword.get(opts, :export),
         bindings: Keyword.get(opts, :bindings, [])
       }}
    end
  end

  @doc """
  I hold every cell value under the widest width I carry, non-negative. Unsigned limbs
  have no negative, so a negative cell is refused by name before the NIF decode crashes.
  """
  @spec fits([[integer()]]) :: :ok | {:error, Refusal.t()}
  def fits(columns) do
    Refusal.refute(List.flatten(columns), &(&1 >= @huge_bound or &1 < 0), fn
      value when value < 0 -> {:witness_value_negative, %{value: value}}
      value -> {:value_exceeds_cell, %{value: value}}
    end)
  end

  # The NIF reads every op as an atom and an integer; add and mul carry an unread zero.
  @spec wire(Uair.op()) :: {atom(), integer()}
  defp wire({op, arg}), do: {op, arg}
  defp wire(op) when is_atom(op), do: {op, 0}

  @doc "I hold every program constant inside the i64 the interpreter reads."
  @spec constants_fit([{atom(), integer()}]) :: :ok | {:error, Refusal.t()}
  def constants_fit(program) do
    Refusal.refute(
      program,
      &match?({:const, k} when abs(k) >= @i64_bound, &1),
      fn {:const, k} -> {:constant_exceeds_cell, %{constant: k}} end
    )
  end

  @spec reads(Uair.mode()) :: [{non_neg_integer(), [non_neg_integer()], non_neg_integer()}]
  defp reads(%Plain{}), do: []

  defp reads(%Composed{reads: reads}),
    do: for(r <- reads, do: {r.value_row, r.bit_rows, r.result_row})

  # The pointer query binds witness columns only; refuse by name before the NIF panics.
  @spec unclaimed(
          [{non_neg_integer(), [non_neg_integer()], non_neg_integer()}],
          non_neg_integer()
        ) :: :ok | {:error, Refusal.t()}
  defp unclaimed(reads, num_public) do
    Refusal.refute(
      Enum.flat_map(reads, fn {value, bits, result} -> [value, result | bits] end),
      &(&1 < num_public),
      &{:read_row_claimed, %{row: &1}}
    )
  end

  @spec cells(Uair.t(), [integer()]) :: cells()
  defp cells(uair, values) do
    cond do
      Enum.any?(values, &(&1 >= @big_bound)) -> {:huge, limbed(uair)}
      Enum.any?(values, &(&1 >= @i64_bound)) -> {:big, limbed(uair)}
      true -> {:i64, uair.columns}
    end
  end

  @spec limbed(Uair.t()) :: [[[non_neg_integer()]]]
  defp limbed(uair),
    do:
      for(
        col <- uair.columns,
        do: for(v <- col, do: v |> Integer.digits(1 <<< 64) |> Enum.reverse())
      )
end
