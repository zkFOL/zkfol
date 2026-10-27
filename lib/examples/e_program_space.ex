defmodule Examples.EProgramSpace do
  @moduledoc "I am the space of programs the grammar writes, every one laid and swept."

  use ExExample

  import ExUnit.Assertions

  alias Examples.EAst
  alias Examples.EForgery
  alias Zkfol.Al
  alias Zkfol.Alloc
  alias Zkfol.Derivation
  alias Zkfol.Interpretation
  alias Zkfol.Lay
  alias Zkfol.Lang.Rel
  alias Zkfol.Lang.Term
  alias Zkfol.Log
  alias Zkfol.Phi
  alias Zkfol.Prover
  alias Zkfol.Semantics
  alias Zkfol.Statement

  @typedoc "One program: the choices that named it, its relations root first, its arguments."
  @type program :: {String.t(), [Rel.t()], [Statement.datum() | :_]}

  @typedoc "One stage of a program: the choice that named it and the relations it stands on."
  @type stage :: {String.t(), [Rel.t()]}

  @doc "I am every composition the grammar writes, each named by its stages."
  @spec space() :: [program()]
  def space() do
    for {producer, prod, datum} <- producers(),
        {middle, mid} <- [{"", []} | banks(:m)],
        {consumer, con} <- consumers() do
      stages = for rels <- [prod, mid, con], rels != [], do: hd(rels).name
      label = [producer, middle, consumer] |> Enum.reject(&(&1 == "")) |> Enum.join(" -> ")
      {label, [chain(stages) | prod ++ mid ++ con], [datum, :_]}
    end
  end

  @doc "What answers lays: the oracle holds it, no forger moves it, and Zinc+ proves it."
  @spec every_program_lays() :: [{String.t(), [Rel.t()], term()}]
  example every_program_lays do
    failing =
      for {{label, rels, args}, proving} <- sample(),
          fault = fault(rels, args, proving),
          do: {label, rels, fault}

    assert failing == [], said(failing)
    failing
  end

  @doc "An unresolved composed output proves on one predicate for different private inputs."
  @spec an_unresolved_output_proves() :: [Lay.t()]
  example an_unresolved_output_proves do
    {_, [root | _] = rels, args} =
      Enum.find(space(), &(elem(&1, 0) == "walk1 -> carried9 -> walk1"))

    {:ok, pred, alloc} = Phi.compile(root, rels, args)
    linked = Alloc.link(pred, alloc)

    for input <- [[1, 2, 3, 4], [5, 6, 7, 8]] do
      assert {:ok, ^pred, ^alloc} = Phi.compile(root, rels, [input, :_])
      {:ok, derivation} = Al.derived(rels, [input, :_])

      assert Derivation.root(derivation, root.name) ==
               {root.name, [input, Enum.map(input, &(&1 * 4)) ++ [18]]}

      lay = Lay.of(derivation, alloc)
      witness = Lay.witness(lay)
      assert Semantics.valid?(linked, witness)
      assert {:ok, %Prover.Report{}, _id} = Prover.prove(linked, witness)

      {:ok, [{_name, row, column} | _cells]} = Lay.claims(lay, [2])

      forged = EAst.tamper(witness, row, column, 1)

      refute Semantics.valid?(linked, forged)
      assert {:error, _refusal} = Prover.prove(linked, forged)
      lay
    end
  end

  # `ZKFOL_PROVE=1` lays every program and proves every tenth; `all` proves them all.
  @spec sample() :: [{program(), boolean()}]
  defp sample() do
    case System.get_env("ZKFOL_PROVE") do
      "all" -> for program <- space(), do: {program, true}
      "1" -> for {program, k} <- Enum.with_index(space()), do: {program, rem(k, 10) == 0}
      _stride -> for program <- Enum.take_every(space(), 77), do: {program, true}
    end
  end

  ############################################################
  #                       The Grammar                        #
  ############################################################

  # A stage taking a bank and making one, so a stage can follow it.
  @spec banks(atom()) :: [stage()]
  defp banks(tag) do
    [
      {"walk1", [walker(tag, 1, :self)]},
      {"walk2", [walker(tag, 2, :self)]},
      {"walk1>2", handoff(tag, 1, 2)},
      {"carried9", [carried(tag, [9])]},
      {"mapped", mapped(tag)},
      {"guarded", [guarded(walker(tag, 1, :self))]}
    ]
  end

  @spec producers() :: [{String.t(), [Rel.t()], Statement.datum()}]
  defp producers() do
    bank = [1, 2, 3, 4]

    [
      {"walk1", [walker(:p, 1, :self)], bank},
      {"walk2", [walker(:p, 2, :self)], bank},
      {"walk2>1", handoff(:p, 2, 1), bank},
      {"matrix", [matrix_rows(:p)], [[1, 2], [3, 4]]},
      {"table0", [table(:p, 0)], 3},
      {"table1", [table(:p, 1)], 3},
      {"shifted", shifted(:p), 3},
      {"reduced", [reduced(:p)], 5}
    ]
  end

  @spec consumers() :: [stage()]
  defp consumers() do
    banks(:c) ++
      [
        {"carried98", [carried(:c, [9, 8])]},
        {"summed", [summed(:c, :after)]},
        {"summed ahead", [summed(:c, :ahead)]},
        {"cell2", [cell_of(:c, :literal)]},
        {"cell1+1", [cell_of(:c, :computed)]},
        {"hopped", hopped(:c)}
      ]
  end

  # The root: each stage handed what the stage before it made.
  @spec chain([atom()]) :: Rel.t()
  defp chain(stages) do
    ports = for k <- 0..length(stages), do: v(:"v#{k}")
    body = for {stage, k} <- Enum.with_index(stages), do: {:call, stage, Enum.slice(ports, k, 2)}
    rel(:main, [{[hd(ports), List.last(ports)], body}])
  end

  ############################################################
  #                      The Combinators                     #
  ############################################################

  # A walk peeling `stride` cells a step and writing as many, doubled.
  @spec walker(atom(), 1 | 2, :self | {:to, Rel.t()}) :: Rel.t()
  defp walker(name, stride, tail) do
    ins = Enum.take([:h, :i], stride)
    outs = Enum.take([:d, :e], stride)
    doubles = for {h, d} <- Enum.zip(ins, outs), do: {:eq, v(d), {:add, v(h), v(h)}}

    rel(name, [
      {[nil, nil], []},
      {[bracket(ins, v(:t)), bracket(outs, v(:s))],
       doubles ++ [{:call, continued(name, tail), [v(:t), v(:s)]}]}
    ])
  end

  # A walk of one stride whose tail is a walk of another.
  @spec handoff(atom(), 1 | 2, 1 | 2) :: [Rel.t()]
  defp handoff(name, stride, rest) do
    tail = walker(:"#{name}_tail", rest, :self)
    [walker(name, stride, {:to, tail}), tail]
  end

  @spec continued(atom(), :self | {:to, Rel.t()}) :: atom()
  defp continued(name, :self), do: name
  defp continued(_name, {:to, %Rel{name: other}}), do: other

  # A bank handed on whole, a literal tacked where it ends.
  @spec carried(atom(), [integer()]) :: Rel.t()
  defp carried(name, literal) do
    rel(name, [
      {[nil, bracket(literal, nil)], []},
      {[bracket([:h], v(:t)), bracket([:h], v(:s))], [{:call, name, [v(:t), v(:s)]}]}
    ])
  end

  # A bank folded to a scalar, the fold written after the call binding its name or ahead of it.
  @spec summed(atom(), :after | :ahead) :: Rel.t()
  defp summed(name, order) do
    call = {:call, name, [v(:t), v(:r)]}
    fold = {:eq, v(:v), {:add, v(:r), v(:h)}}

    rel(name, [
      {[nil, 0], []},
      {[bracket([:h], v(:t)), v(:v)], if(order == :after, do: [call, fold], else: [fold, call])}
    ])
  end

  # A row of two is a cell of the walk: the pair sums where the row stands.
  @spec matrix_rows(atom()) :: Rel.t()
  defp matrix_rows(name) do
    rel(name, [
      {[nil, nil], []},
      {[bracket([bracket([:x, :y], nil)], v(:t)), bracket([:s], v(:r))],
       [{:eq, v(:s), {:add, v(:x), v(:y)}}, {:call, name, [v(:t), v(:r)]}]}
    ])
  end

  # A scalar index counting down to `base`, a cell of the bank a step.
  @spec table(atom(), 0 | 1) :: Rel.t()
  defp table(name, base) do
    rel(name, [
      {[base, nil], []},
      {[v(:x), bracket([:v], v(:t))],
       [
         {:call, &Zkfol.Prims.gt/0, [v(:x), base, v(:_s0)]},
         {:call, name, [{:add, v(:x), -1}, v(:t)]},
         {:eq, v(:v), {:add, v(:x), v(:x)}}
       ]}
    ])
  end

  # A walk down a scalar index reading a table an offset back.
  @spec shifted(atom()) :: [Rel.t()]
  defp shifted(name) do
    facts = :"#{name}_tab"

    [
      rel(name, [
        {[1, bracket([10], nil)], []},
        {[v(:x), bracket([:v], v(:t))],
         [
           {:call, &Zkfol.Prims.gt/0, [v(:x), 1, v(:_s0)]},
           {:call, name, [{:add, v(:x), -1}, v(:t)]},
           {:call, facts, [{:add, v(:x), -1}, v(:v)]}
         ]}
      ]),
      rel(facts, for({x, y} <- [{1, 10}, {2, 20}, {3, 30}, {4, 40}], do: {[x, y], []}))
    ]
  end

  # A scalar walk reducing under a modulus, the quotient riding beside each value.
  @spec reduced(atom()) :: Rel.t()
  defp reduced(name) do
    rel(name, [
      {[1, bracket([1, 0], nil)], []},
      {[2, bracket([1, 0, 1, 0], nil)], []},
      {[v(:x), bracket([:v, :q, :a, :i, :b, :j], v(:t))],
       [
         {:call, &Zkfol.Prims.gt/0, [v(:x), 2, v(:_s0)]},
         {:call, name, [{:add, v(:x), -1}, bracket([:a, :i, :b, :j], v(:t))]},
         {:eq, {:add, v(:a), v(:b)}, {:add, {:mul, v(:q), 7919}, v(:v)}},
         {:call, &Zkfol.Prims.lt/0, [v(:v), 7919, v(:_s1)]},
         {:call, &Zkfol.Prims.gt/0, [{:add, v(:v), 1}, 0, v(:_s2)]},
         {:call, &Zkfol.Prims.gt/0, [{:add, v(:q), 1}, 0, v(:_s3)]}
       ]}
    ])
  end

  # A cell read off the bank: at a literal index, or at one the body computes.
  @spec cell_of(atom(), :literal | :computed) :: Rel.t()
  defp cell_of(name, :literal),
    do: rel(name, [{[v(:xs), v(:v)], [{:call, &Zkfol.Prims.nth/0, [2, v(:xs), v(:v)]}]}])

  defp cell_of(name, :computed),
    do:
      rel(name, [
        {[v(:xs), v(:v)],
         [{:eq, v(:k), {:add, 1, 1}}, {:call, &Zkfol.Prims.nth/0, [v(:k), v(:xs), v(:v)]}]}
      ])

  # A chain no column counts: a cell of the bank aims a walk that reaches itself.
  @spec hopped(atom()) :: [Rel.t()]
  defp hopped(name) do
    down = :"#{name}_down"

    [
      rel(name, [
        {[v(:xs), v(:r)],
         [
           {:call, &Zkfol.Prims.nth/0, [1, v(:xs), v(:h)]},
           {:call, &Zkfol.Prims.mod/0, [v(:h), 3, v(:k), v(:_q0)]},
           {:call, down, [v(:k), v(:r)]}
         ]}
      ]),
      rel(down, [
        {[0, 0], []},
        {[v(:x), v(:r)],
         [
           {:call, &Zkfol.Prims.gt/0, [v(:x), 0, v(:_s0)]},
           {:eq, v(:y), {:add, v(:x), -1}},
           {:call, down, [v(:y), v(:z)]},
           {:eq, v(:r), {:add, v(:z), 1}}
         ]}
      ])
    ]
  end

  # A relation passed by name: the walk calls what it is handed.
  @spec mapped(atom()) :: [Rel.t()]
  defp mapped(name) do
    each = :"#{name}_each"
    succ = :"#{name}_succ"

    [
      rel(name, [{[v(:xs), v(:ys)], [{:call, each, [v(:xs), {:papply, succ, []}, v(:ys)]}]}]),
      rel(each, [
        {[nil, v(:_r), nil], []},
        {[bracket([:h], v(:t)), v(:r), bracket([:g], v(:s))],
         [{:call, {:var, :r}, [v(:h), v(:g)]}, {:call, each, [v(:t), v(:r), v(:s)]}]}
      ]),
      rel(succ, [{[v(:x), v(:y)], [{:eq, v(:y), {:add, v(:x), 1}}]}])
    ]
  end

  # A comparison in the walk's body: the guard's slack rides in the predicate.
  @spec guarded(Rel.t()) :: Rel.t()
  defp guarded(rel = %Rel{clauses: clauses}),
    do: %{rel | clauses: for({head, body} <- clauses, do: {head, body ++ compared(head)})}

  @spec compared([Term.t()]) :: [Term.goal()]
  defp compared([{:cons, {:var, x}, _rest} | _args]),
    do: [{:call, &Zkfol.Prims.gt/0, [v(x), 0, v(:_s0)]}]

  defp compared(_head), do: []

  @spec rel(atom(), [{[Term.t()], [Term.goal()]}]) :: Rel.t()
  defp rel(name, clauses),
    do: %Rel{name: name, arity: clauses |> hd() |> elem(0) |> length(), clauses: clauses}

  @spec bracket([atom() | Term.t()], Term.t()) :: Term.t()
  defp bracket(cells, tail),
    do: List.foldr(cells, tail, &{:cons, if(is_atom(&1), do: v(&1), else: &1), &2})

  @spec v(atom()) :: Term.t()
  defp v(name), do: {:var, name}

  ############################################################
  #                       The Property                       #
  ############################################################

  @spec fault([Rel.t()], [Statement.datum() | :_], boolean()) :: term() | nil
  defp fault(rels, args, proving) do
    with %Statement{} = statement <- solved(rels, args),
         :ok <- columns(statement),
         :ok <- swept(statement),
         :ok <- placed(statement),
         :ok <- proved(statement, proving),
         do: nil
  end

  # A run that derived nothing is the one refusal the space expects; any other is a fault.
  @spec solved([Rel.t()], [Statement.datum() | :_]) :: Statement.t() | nil | {:unsolved, term()}
  defp solved(rels, args) do
    ran = Zkfol.emit(rels, args: args)

    case {Log.Run.final_stage(ran), Log.refusal(Log.snapshot(), ran)} do
      {%Statement{stage: %Statement.Solved{}} = statement, _none} -> statement
      {_short, {:no_answer, _detail}} -> nil
      {_short, refusal} -> {:unsolved, refusal}
    end
  end

  @spec columns(Statement.t()) :: :ok | {:column, pos_integer()}
  defp columns(statement) do
    pred = Statement.pred(statement)
    witness = Statement.witness(statement)

    case Enum.find(1..Interpretation.len(witness), &(not Semantics.holds?(pred, witness, &1))) do
      nil -> :ok
      x -> {:column, x}
    end
  end

  @spec swept(Statement.t()) :: :ok | {:forgeable, [EForgery.move()]}
  defp swept(statement) do
    case EForgery.sweep(statement) do
      {_believed, []} -> :ok
      {_believed, surprising} -> {:forgeable, surprising}
    end
  end

  @spec placed(Statement.t()) :: :ok | {:misplaced, [{integer(), {:ok, integer()} | :error}]}
  defp placed(statement) do
    case Enum.reject(EForgery.placing(statement), fn {cell, at} -> at == {:ok, cell} end) do
      [] -> :ok
      dropped -> {:misplaced, dropped}
    end
  end

  @spec proved(Statement.t(), boolean()) :: :ok | {:unproved, term()}
  defp proved(_statement, false), do: :ok

  defp proved(statement, true) do
    case Prover.prove(Statement.pred(statement), Statement.witness(statement),
           claims: Statement.claims(statement)
         ) do
      {:ok, %Prover.Report{}, _id} -> :ok
      {:error, refusal} -> {:unproved, refusal}
    end
  end

  @spec said([{String.t(), [Rel.t()], term()}]) :: String.t()
  defp said(failing) do
    Enum.map_join(failing, "\n\n", fn {label, rels, fault} ->
      clauses = Enum.map_join(rels, "\n", &"  #{&1.name}/#{&1.arity} #{inspect(&1.clauses)}")
      "#{label}: #{inspect(fault, limit: 12)}\n#{clauses}"
    end)
  end
end
