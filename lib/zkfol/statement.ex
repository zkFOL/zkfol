defmodule Zkfol.Statement do
  @moduledoc """
  I am one statement of the logic: its relations, the arguments of the instance, and
  the stage the pipeline has carried it to.
  """

  use TypedStruct

  alias Zkfol.Ast
  alias Zkfol.Interpretation
  alias Zkfol.Lang.Rel
  alias Zkfol.Refusal
  alias Zkfol.Statement.Solved

  @typedoc "How far the pipeline has carried a statement."
  @type stage :: :raw | Zkfol.Derivation.t() | Solved.t()

  @typedoc "What an argument carries: one number, or the sequence a bracket writes."
  @type datum :: integer() | [datum()]

  typedstruct enforce: true do
    field(:rels, [Zkfol.Lang.Rel.t()], default: [])
    field(:args, [datum() | :_], default: [])
    field(:stage, stage(), default: :raw)
  end

  @doc "I am the statement `target` stands for, root first, `opts[:args]` its arguments."
  @spec of(t() | Rel.t() | [Rel.t()], keyword()) :: t()
  def of(target, opts \\ [])
  def of(statement = %__MODULE__{}, _opts), do: statement
  def of(root = %Rel{}, opts), do: %__MODULE__{rels: [root], args: args(opts)}
  def of(rels, opts) when is_list(rels), do: %__MODULE__{rels: rels, args: args(opts)}

  @spec args(keyword()) :: [datum() | :_]
  defp args(opts), do: Keyword.get(opts, :args, [])

  @doc "I am the predicate the statement's relations lower to, linked, once solved."
  @spec pred(t()) :: Ast.pred()
  def pred(%__MODULE__{stage: %Solved{pred: pred}}), do: pred

  @doc "I am the witness the lay stands, once solved."
  @spec witness(t()) :: Interpretation.t()
  def witness(%__MODULE__{stage: %Solved{lay: lay}}), do: Zkfol.Lay.witness(lay)

  @doc "I am the claims an act opened on me, none before one has."
  @spec claims(t()) :: [Interpretation.claim()]
  def claims(%__MODULE__{stage: %Solved{claims: claims}}), do: claims
  def claims(%__MODULE__{}), do: []

  @doc "I am the statement with the cells `public` opens claimed, refusing one already claimed."
  @spec opened(t(), [Zkfol.Lay.opening()]) :: {:ok, t()} | {:error, Refusal.t()}
  def opened(%__MODULE__{stage: %Solved{claims: [_one | _rest] = claims}}, _public),
    do: {:error, {:publicity_is_the_acts, %{claims: claims}}}

  def opened(statement = %__MODULE__{stage: solved = %Solved{lay: lay}}, public) do
    with {:ok, claims} <- Zkfol.Lay.claims(lay, public),
         do: {:ok, %{statement | stage: %{solved | claims: claims}}}
  end

  def opened(statement = %__MODULE__{}, []), do: {:ok, statement}

  def opened(%__MODULE__{}, [named | _rest]),
    do: {:error, {:unbound_variable, %{variable: named}}}

  @doc "I am the rows of `sym`'s bank in my witness."
  @spec bank(t(), atom()) :: [[non_neg_integer()]]
  def bank(statement = %__MODULE__{}, sym) do
    laid = Interpretation.rows(witness(statement))
    for i <- Zkfol.Alloc.rows(alloc(statement), sym), do: Enum.at(laid, i - 1)
  end

  @doc "I am the lay a run produced, nil before one has."
  @spec lay(t()) :: Zkfol.Lay.t() | nil
  def lay(%__MODULE__{stage: %Solved{lay: lay}}), do: lay
  def lay(%__MODULE__{}), do: nil

  @doc "I am the allocation, read off the lay."
  @spec alloc(t()) :: Zkfol.Alloc.t() | nil
  def alloc(statement = %__MODULE__{}),
    do: with(%Zkfol.Lay{} = lay <- lay(statement), do: lay.alloc)

  @doc "I am the compiler's retained walk: its clause inputs, bindings and constraints."
  @spec lowering(t()) :: [Zkfol.Phi.Clause.t()] | nil
  def lowering(%__MODULE__{stage: %Solved{lowering: lowering}}), do: lowering
  def lowering(%__MODULE__{}), do: nil

  @doc "I am the derivation: the run's own once derived, the lay's once solved."
  @spec derivation(t()) :: Zkfol.Derivation.t() | nil
  def derivation(%__MODULE__{stage: derivation = %Zkfol.Derivation{}}), do: derivation

  def derivation(statement = %__MODULE__{}),
    do: with(%Zkfol.Lay{} = lay <- lay(statement), do: lay.derivation)

  @doc "I am the statement carrying `derivation`: what its relations established, unlaid."
  @spec derived(t(), Zkfol.Derivation.t()) :: t()
  def derived(statement = %__MODULE__{}, derivation),
    do: %{statement | stage: derivation}

  @doc "I am the statement beneath the `k`-th fact of my derivation, nil without one."
  @spec under(t(), pos_integer()) :: t() | nil
  def under(statement = %__MODULE__{rels: rels}, k) when is_integer(k) do
    with %Zkfol.Derivation{facts: facts} = d <- derivation(statement),
         {name, tuple} = fact <- Enum.at(facts, k - 1),
         root when not is_nil(root) <- Enum.find(rels, &(&1.name == name)),
         source = %{statement | rels: [root | List.delete(rels, root)], args: tuple},
         {:ok, sub} <- Zkfol.Phi.relaid(source, Zkfol.Derivation.under(d, fact)) do
      sub
    else
      _nothing -> nil
    end
  end
end
