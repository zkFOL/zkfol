defmodule Zkfol.Phi do
  @moduledoc """
  I compile relations into constraints and an allocation, then fill that allocation
  from an AL derivation.

  `Zkfol.Unfold` unfolds the clauses first and makes every choice: which calls are
  replaced by their clause, which walk an array, which names need cells.
  `Zkfol.Phi.Storage` then decides how each parameter is stored. I compile what is left
  without choosing. A member is a relation with its specialised parameters. Each of its
  clauses matches its head against the parameters, then compiles in order:

      p(args)          the callee is present at the call's address; a pointer call
                       matches its arguments against the callee's parameters there
      a = b            one side is matched against the value of the other
      a primitive      its constraint over the numbers and cells it reads

  ### Public API

  - `run/2`, `verb/0`: the pipeline pass.
  - `relaid/2`: compile a derived statement and construct its witness.
  - `compile/3`: return the predicate and allocation.
  - `lower/2`: return the predicate with allocated row numbers.
  """

  @behaviour Zkfol.Pipeline

  use TypedStruct

  alias Zkfol.Alloc
  alias Zkfol.Alloc.{Bank, Member, Site, Slot}
  alias Zkfol.Ast
  alias Zkfol.Derivation
  alias Zkfol.Lang
  alias Zkfol.Lang.{Rel, Term}
  alias Zkfol.Lay
  alias Zkfol.Nodes
  alias Zkfol.Phi.{Match, Storage, Walk}
  alias Zkfol.Phi.Storage.Interface
  alias Zkfol.Refusal
  alias Zkfol.Statement
  alias Zkfol.Unfold
  alias Zkfol.Unfold.{Call, Primitive}

  typedstruct module: Clause, enforce: true do
    @moduledoc "I am a source clause of a member and the walk it compiled to."
    field(:member, atom())
    field(:head, [Zkfol.Lang.Term.t()])
    field(:body, [Zkfol.Lang.Term.goal()])
    field(:compiled, Zkfol.Phi.Walk.t() | :dead)
  end

  @typep storage :: %{Unfold.key() => Interface.t()}

  @typep unit :: %{member: Member.t(), pred: Ast.pred(), banks: [Bank.t()], clauses: [Clause.t()]}

  @doc "I lay a derived statement; one that has not run passes through."
  @impl Zkfol.Pipeline
  @spec run(Statement.t(), keyword()) :: {:ok, Statement.t()} | {:error, Refusal.t()}
  def run(statement = %Statement{stage: %Derivation{} = derivation}, _opts),
    do: relaid(statement, derivation)

  def run(statement = %Statement{}, _opts), do: {:ok, statement}

  @impl Zkfol.Pipeline
  @spec verb() :: Zkfol.Pipeline.result()
  def verb, do: :lowers

  @doc "I lay the derivation for the statement."
  @spec relaid(Statement.t(), Derivation.t()) :: {:ok, Statement.t()} | {:error, Refusal.t()}
  def relaid(statement = %Statement{rels: [root | _rest] = rels}, derivation = %Derivation{}) do
    # What the run established of the root itself: the arguments, every hole filled.
    {_name, args} = Derivation.root(derivation, root.name) || {root.name, []}

    with {:ok, pred, alloc, clauses} <- lowered(root, rels, args) do
      stage = %Statement.Solved{
        pred: Alloc.link(pred, alloc),
        lay: Lay.of(derivation, alloc),
        lowering: clauses
      }

      {:ok, %{statement | stage: stage}}
    end
  end

  @doc "I am the predicate of `root` against `rels`, linked."
  @spec lower(Rel.t(), [Rel.t()]) :: {:ok, Ast.pred()} | {:error, Refusal.t()}
  def lower(root = %Rel{}, rels) do
    with {:ok, pred, alloc} <- compile(root, rels), do: {:ok, Alloc.link(pred, alloc)}
  end

  @doc "I compile `root`; argument values stay private, only their kind is read."
  @spec compile(Rel.t(), [Rel.t()] | nil, [term()]) ::
          {:ok, Ast.pred(), Alloc.t()} | {:error, Refusal.t()}
  def compile(root = %Rel{}, rels \\ nil, args \\ []) do
    with {:ok, pred, alloc, _clauses} <- lowered(root, rels, args), do: {:ok, pred, alloc}
  end

  @spec lowered(Rel.t(), [Rel.t()] | nil, [term()]) ::
          {:ok, Ast.pred(), Alloc.t(), [Clause.t()]} | {:error, Refusal.t()}
  defp lowered(root, rels, args) do
    with {:ok, [root | _rest] = reached} <- Lang.reached(root, rels || [root]) do
      scope = Map.new(reached, &{&1.name, &1})
      program = Unfold.program(root, scope)
      storage = Storage.of(program, scope, args)

      units =
        for {key = {name, _handed}, clauses} <- program,
            do: member(key, clauses, scope[name].clauses, storage)

      preds = Enum.map(units, & &1.pred)
      members = Enum.flat_map(units, &[&1.member | &1.banks])

      runs =
        for unit <- units,
            %Slot{allocation: {:bank, bank, extent}} <- unit.member.slots,
            do: runs(bank, extent)

      {pred, members} = Nodes.lower(Ast.conj(preds ++ runs), members)
      {:ok, pred, Alloc.numbered(members, root.name), Enum.flat_map(units, & &1.clauses)}
    end
  catch
    {:refused, refusal} -> {:error, refusal}
  end

  # A bank's presence is one on the run from column two to its last element: the run
  # starts at column two, has no gap and reaches the last element, so a forger cannot
  # shorten a walk.
  @spec runs(atom(), non_neg_integer()) :: Ast.pred()
  defp runs(name, extent) do
    unbroken =
      Ast.disj([
        Ast.eq({:cell, {:in, name}}, 0),
        Ast.eq(Ast.at({:in, name}, :x, 1, -1), 1),
        Ast.eq(:x, 2)
      ])

    if extent == 0,
      do: unbroken,
      else: Ast.conj([unbroken, Ast.eq(Ast.at({:in, name}, :x, 0, extent + 1), 1)])
  end

  ############################################################
  #                         Members                          #
  ############################################################

  # The member's predicate: it is absent, or one of its clauses holds.
  @spec member(Unfold.key(), [Unfold.Clause.t()], [{[Term.t()], [Term.goal()]}], storage()) ::
          unit()
  defp member(key, clauses, source, storage) do
    interface = %Interface{name: name} = Map.fetch!(storage, key)
    walks = for {clause, c} <- Enum.with_index(clauses), do: clause(clause, c, interface, storage)
    live = for walk = %Walk{} <- walks, do: walk
    present = Ast.cell({:in, name})

    branches =
      for walk <- live, do: Ast.conj([Ast.eq(present, 1) | Enum.sort_by(walk.eqs, &inspect/1)])

    local = live |> Enum.flat_map(& &1.slots) |> Enum.sort_by(&elem(&1.allocation, 1))

    sites =
      Map.new(Enum.with_index(walks), fn
        {%Walk{sites: sites}, c} -> {c, Enum.reverse(sites)}
        {:dead, c} -> {c, []}
      end)

    %{
      member: %Member{
        name: name,
        relation: interface.relation,
        steps: interface.steps,
        slots: interface.slots ++ local,
        sites: sites
      },
      pred: Ast.disj([Ast.eq(present, 0) | branches]),
      banks: interface.banks,
      clauses:
        for {{head, body}, walk} <- Enum.zip(source, walks) do
          %Clause{member: name, head: head, body: body, compiled: walk}
        end
    }
  end

  # I match the head against the parameters, then compile the calls, the equations and
  # the primitives in that order.
  @spec clause(Unfold.Clause.t(), non_neg_integer(), Interface.t(), storage()) ::
          Walk.t() | :dead
  defp clause(clause, c, interface, storage) do
    walk = Walk.allocate(%Walk{member: interface.name, clause: c}, clause.own_cells)

    with walk = %Walk{} <- Match.matches(stored(clause.head, interface.values), walk),
         walk = %Walk{} <- Walk.each(clause.calls, walk, &call(&1, &2, storage)),
         walk = %Walk{} <-
           Walk.each(clause.equations, walk, fn {a, b}, walk -> Match.equal(a, b, walk) end) do
      Enum.reduce(clause.primitives, walk, &primitive/2)
    end
  end

  # Each term with its parameter's value; a parameter without storage is skipped.
  @spec stored([Term.t()], [Match.value() | nil]) :: [{Term.t(), Match.value()}]
  defp stored(terms, values),
    do: for({term, value} <- Enum.zip(terms, values), value != nil, do: {term, value})

  # The callee is present at the call's address, and the arguments are matched against
  # its parameters there. A walk passes none: it reads the caller's cells directly.
  @spec call(Call.t(), Walk.t(), storage()) :: Match.result()
  defp call(%Call{source: source, member: key, args: args, at: at}, walk, storage) do
    %Interface{name: callee, values: values} = Map.fetch!(storage, key)
    {address = {:at, base, m, a}, slots} = address(at, callee, source, walk)
    site = %Site{callee: callee, address: address, source: source}
    walk = %{walk | sites: [site | walk.sites], slots: slots ++ walk.slots}
    walk = Walk.constrain(walk, [Ast.eq(Ast.at({:in, callee}, base, m, a), 1)])
    there = for {arg, value} <- stored(args, values), do: {arg, Match.frame(value, address)}
    Match.matches(there, walk)
  end

  # The callee's column: named by a pointer cell of the call, the first column of a walk,
  # or one column back inside a walk.
  @spec address(Unfold.at(), atom(), [Unfold.step()], Walk.t()) :: {Ast.address(), [Slot.t()]}
  defp address(:pointer, callee, source, walk) do
    pointer = {walk.member, {:own, {:"which #{callee}", source ++ [walk.clause]}}}
    slot = %Slot{name: :"which #{callee}", allocation: {:cell, pointer}}
    {Ast.address({:cell, pointer}, 1, 0), [slot]}
  end

  defp address({:entry, extent}, _callee, _source, _walk),
    do: {Ast.address(:x, 0, extent + 1), []}

  defp address(:back, _callee, _source, _walk), do: {Ast.address(:x, 1, -1), []}

  # The list argument of a primitive is read as cells and every other one as a number.
  @lists %{natural: nil, nth: 1, distinct: 0, permutation: 1}

  @spec primitive(Primitive.t(), Walk.t()) :: Walk.t()
  defp primitive(%Primitive{op: op, args: args}, walk) do
    read = fn {arg, k} ->
      value = Match.value(arg, walk.env)
      if k == @lists[op], do: Match.cells(value), else: Match.scalar(value)
    end

    Walk.constrain(walk, Ast.folded(apply(Ast, op, Enum.map(Enum.with_index(args), read))))
  end
end
