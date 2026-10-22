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

  @typedoc "A word lookup: {column, table width}."
  @type lookup :: {non_neg_integer(), pos_integer()}

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

  `export: prefix` writes the statement to `prefix.json` and the proof to `prefix.proof`, for
  `priv/native/zkfol_verify`. Zinc+ is not zero-knowledge: the proof reveals part of the witness.

  `unchecked: true` ships the payload as built, past `fits/1`. It is the door the
  negative tests need: a forgery the circuit must refuse cannot be watched being
  refused while Elixir refuses it first. No ordinary caller passes it.
  """
  @spec request(Uair.t(), keyword()) :: {:ok, pos_integer()} | {:error, Refusal.t()}
  def request(uair = %Uair{}, opts \\ []) do
    values = List.flatten(uair.columns)
    reads = reads(uair.mode)

    with :ok <- unclaimed(reads, uair.num_public),
         :ok <- if(Keyword.get(opts, :unchecked, false), do: :ok, else: fits(uair.columns)) do
      queued =
        Zkfol.ZincPlus.Native.prove_fol(
          uair,
          cells(uair, values),
          Uair.num_vars(uair),
          Uair.word_lookups(uair),
          reads,
          Keyword.get(opts, :export)
        )

      with {:error, said} <- queued, do: {:error, Refusal.from_backend(said)}
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

  @doc "I hold every program constant inside the i64 the interpreter reads."
  @spec constants_fit([Uair.op()]) :: :ok | {:error, Refusal.t()}
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
