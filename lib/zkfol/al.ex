defmodule Zkfol.Al do
  @moduledoc """
  I am the AL backend: a statement becomes clauses and runs as written,
  so the derivation is the witness. For derivation, each generated method carries its
  source bindings in one final internal argument; questions leave that argument empty.
  """

  alias AL.Syntax.Printer
  alias Zkfol.Al.Ask
  alias Zkfol.Derivation
  alias Zkfol.Program
  alias Zkfol.Lang.Rel
  alias Zkfol.Lang.Term
  alias Zkfol.Ast
  alias Zkfol.Refusal
  alias Zkfol.Log
  alias Zkfol.Statement

  @heap 256_000_000

  # The names I make begin `_` and a capital; a surface name never capitalises to one.
  @self AL.Var.var("_Self")
  @len AL.Var.var("_Len")
  @ask AL.Var.var("_Ask")
  @bindings AL.Var.var("_Bindings")

  @typedoc "An emitted AL program: AL source text, ready for AL.run/3."
  @type program :: String.t()

  @doc "I am the installed program owned by this ask."
  @spec program(Ask.t()) :: AL.Object.t()
  def program(%Ask{class: class, branch: branch}), do: %AL.Object{id: class, branch: branch.id}

  @doc "I am the derivation `arguments` establish: one ask, run once to its first answer."
  @spec derived(Statement.t() | Rel.t() | [Rel.t()], [Statement.datum() | :_], keyword()) ::
          {:ok, Derivation.t()} | {:error, Refusal.t()}
  def derived(target, arguments, opts \\ []) do
    with {:ok, ask} <- open(target, arguments, opts, :derivation) do
      name = Keyword.get(opts, :name, hd(ask.rels).name)

      case capped_eval(ask) do
        {:ok, _bindings, derivation} ->
          count = length(derivation.facts)
          event = {:al_solved, %{name: name, count: count, program: program(ask)}}
          Log.push(event, Keyword.get(opts, :basedon))

          {:ok, derivation}

        {:no, _reason} ->
          {:error, {:no_answer, %{relation: name}}}

        {:error, _reason} = refusal ->
          refusal
      end
    end
  end

  @doc """
  I open a stepping ask at `arguments`: the question installed on the branch it lands on,
  the goal against it. The ask holds AL's search state, so whoever opens it steps it.
  """
  @spec open(Statement.t() | Rel.t() | [Rel.t()], [Statement.datum() | :_], keyword()) ::
          {:ok, Ask.t()} | {:error, Refusal.t()}
  def open(target, arguments, opts), do: open(target, arguments, opts, :question)

  @spec open(
          Statement.t() | Rel.t() | [Rel.t()],
          [Statement.datum() | :_],
          keyword(),
          :question | :derivation
        ) :: {:ok, Ask.t()} | {:error, Refusal.t()}
  defp open(target, arguments, opts, mode) do
    with {:ok, [root | _rest] = rels} <- rels(target),
         {:ok, arguments} <- padded(arguments, root.arity),
         len? = Enum.any?(rels, &mentions_len?(&1.clauses)),
         :ok <- len_bound(len?, arguments),
         branch = %AL.Branch{id: landing(Keyword.get(opts, :branch))},
         {:ok, program} <-
           question_program(Enum.map(rels, &implementation(&1, mode)), len?, mode),
         {:ok, class} <- install(program, branch) do
      {:ok,
       %Ask{
         rels: rels,
         goal: asking(root, arguments, len?, class),
         class: class,
         arguments: arguments,
         branch: branch,
         heap: Keyword.get(opts, :heap) || @heap,
         len?: len?
       }}
    end
  end

  @doc "I take the ask's next answer, and the ask to step again."
  @spec step(Ask.t()) :: {Ask.outcome(), Ask.t()}
  def step(ask = %Ask{state: nil}), do: answered(AL.run(ask.goal, ask.branch), ask)
  def step(ask = %Ask{state: state}), do: answered(AL.next_solution(state), ask)

  # A closing ask unbinds every method on its own object; nothing reaches their clauses after.
  @retraction ~S"forall {method Ask Name Impl} {vm_retract_method Ask Name Impl}."

  @doc "I retract this ask’s methods; other installations keep theirs."
  @spec close(Ask.t()) :: :ok | {:error, Refusal.t()}
  def close(%Ask{branch: branch, class: class}) do
    with {:ok, _bindings} <- run(@retraction, branch, bindings: %{"Ask" => class}), do: :ok
  end

  @spec answered(term(), Ask.t()) :: {Ask.outcome(), Ask.t()}
  defp answered(evaluated, ask) do
    case outcome(evaluated) do
      {:ok, bindings, state} -> {ground(bindings, ask.arguments), %{ask | state: state}}
      {:no, _reason} -> {:exhausted, ask}
      {:error, _reason} = refusal -> {refusal, ask}
    end
  end

  @spec ground(%{String.t() => term()}, [Statement.datum() | :_]) ::
          {:ok, [Statement.datum()]} | {:error, Refusal.t()}
  defp ground(bindings, arguments) do
    answer =
      for {argument, row} <- Enum.with_index(arguments, 1),
          do: if(argument == :_, do: bindings[AL.Var.key(query(row))], else: argument)

    if Enum.all?(answer, &ground?/1),
      do: {:ok, answer},
      else: {:error, {:residue, %{answer: answer}}}
  end

  # A run that built a sequence leaves the tail open until the last call closes it.
  @spec ground?(term()) :: boolean()
  defp ground?(q) when is_integer(q), do: true
  defp ground?(cells) when is_list(cells), do: Enum.all?(cells, &ground?/1)
  defp ground?(_open), do: false

  @spec rels(Statement.t() | Rel.t() | [Rel.t()]) :: {:ok, [Rel.t()]} | {:error, Refusal.t()}
  defp rels(%Statement{rels: [root | _rest] = rels}), do: Program.reached(root, rels)
  defp rels(root = %Rel{}), do: Program.reached(root, [root])
  defp rels([root = %Rel{} | _rest] = list), do: Program.reached(root, list)
  defp rels(_none), do: {:error, {:no_relations, %{}}}

  # A question can use a native definition; a derivation needs the source calls as well.
  @spec implementation(Rel.t(), :question | :derivation) :: Rel.t()
  defp implementation(rel = %Rel{al: {:definition, al}}, :question),
    do: %{rel | al: al, clauses: for({head, _body} <- rel.clauses, do: {head, []})}

  defp implementation(rel = %Rel{al: {:definition, al}}, :derivation), do: %{rel | al: al}
  defp implementation(rel, _mode), do: rel

  # len names the trace, which only a bound count sizes ahead of time.
  @spec len_bound(boolean(), [Statement.datum() | :_]) :: :ok | {:error, Refusal.t()}
  defp len_bound(false, _args), do: :ok
  defp len_bound(true, [count | _rest]) when not is_atom(count), do: :ok
  defp len_bound(true, _args), do: {:error, {:len_needs_a_bound_count, %{}}}

  # The root call: a bound row's value, a query variable elsewhere, the size last where len asks.
  @spec asking(Rel.t(), [Statement.datum() | :_], boolean(), atom()) :: program()
  defp asking(root, arguments, len?, class) do
    args =
      Enum.with_index(arguments, 1)
      |> Enum.map(fn
        {:_, row} -> query(row)
        {name, _row} when is_atom(name) -> var(name)
        {value, _row} -> value
      end)

    sized = if len?, do: [hd(arguments)], else: []
    Printer.program([call(method(root.name), [class | args ++ sized ++ [@bindings]])])
  end

  # AL keeps every call under the frame that made it, so its journal is the derivation. The
  # heap cap is ours, not AL's, and an exit reason is copied onto the parent's uncapped heap,
  # so the child sheds the state and only the derivation leaves.
  @spec capped_eval(Ask.t()) ::
          {:ok, AL.Var.store(), Derivation.t()} | {:no, term()} | {:error, Refusal.t()}
  defp capped_eval(ask = %Ask{}) do
    names = Map.new(ask.rels, &{method(&1.name), {&1.name, &1.arity}})

    {pid, ref} =
      spawn_monitor(fn ->
        Process.flag(:max_heap_size, %{size: ask.heap, kill: true, error_logger: false})

        exit(
          {:derived,
           case AL.run(ask.goal, ask.branch, trace: [:domino]) do
             %AL{result: {:atomic, {bindings, constraints, state}}} ->
               {:atomic, {bindings, constraints, Derivation.of(state, names, ask.len?)}}

             unanswered ->
               unanswered
           end}
        )
      end)

    receive do
      {:DOWN, ^ref, :process, ^pid, {:derived, result}} ->
        outcome(result)

      {:DOWN, ^ref, :process, ^pid, _killed} ->
        outcome({:error, "the derivation exceeded #{ask.heap} heap words"})
    end
  end

  # An argument past the last row addresses nothing; zipping it away would answer another ask.
  @spec padded([Statement.datum() | :_], non_neg_integer()) ::
          {:ok, [Statement.datum() | :_]} | {:error, Refusal.t()}
  defp padded(args, arity) when length(args) > arity,
    do: {:error, {:arguments_exceed_rows, %{args: length(args), rows: arity}}}

  defp padded(args, arity), do: {:ok, args ++ List.duplicate(:_, arity - length(args))}

  # A search stopped by the budget never reached a no, so it refuses as itself.
  @spec outcome(term()) ::
          {:ok, %{String.t() => term()}, term()} | {:no, term()} | {:error, Refusal.t()}
  defp outcome(%AL{result: result}), do: outcome(result)
  defp outcome({:atomic, {bindings, _constraints, state}}), do: {:ok, bindings, state}

  defp outcome({:aborted, %{reason: {:resource_limit_exceeded, n}}}),
    do: {:error, {:unresolved_within_budget, %{reductions: n}}}

  defp outcome({:aborted, reason}), do: {:no, reason}
  defp outcome(exceeded), do: Refusal.from_al(exceeded)

  @spec question_program([Rel.t()], boolean(), :question | :derivation) ::
          {:ok, program()} | {:error, Refusal.t()}
  defp question_program(rels, len?, mode) do
    hints =
      Map.new(
        for %Rel{al: al, clauses: [{head, _body} | _rest]} = rel <- rels,
            al != nil,
            do: {rel.name, {head, al}}
      )

    # A relation with no clauses of its own says nothing a send could add.
    said =
      MapSet.new(
        for %Rel{al: al, clauses: clauses} = rel <- rels,
            al != nil,
            Enum.all?(clauses, fn {_head, body} -> body == [] end),
            do: rel.name
      )

    rels
    |> Enum.flat_map(fn rel -> Enum.map(rel.clauses, &{rel.name, rel.al, &1}) end)
    |> Enum.with_index()
    |> Refusal.map(fn {{rname, al, clause}, i} ->
      question_clause(rname, al, clause, i, len?, hints, said, mode)
    end)
    |> case do
      {:ok, clauses} -> {:ok, installed(clauses)}
      refusal -> refusal
    end
  end

  @spec question_clause(
          atom(),
          String.t() | nil,
          {[term()], [term()]},
          non_neg_integer(),
          boolean(),
          %{atom() => {[term()], String.t()}},
          MapSet.t(),
          :question | :derivation
        ) :: {:ok, String.t()} | {:error, Refusal.t()}
  defp question_clause(rname, al, {head, body}, i, len?, hints, said, mode) do
    case Enum.find(head, &(not Term.seatable?(&1))) do
      nil ->
        lenp = if len?, do: [@len], else: []
        reading = if al, do: saying(al, %{}), else: []
        # Bind the bundle in the head so it follows this clause through backtracking.
        names = if mode == :derivation, do: Enum.uniq(Term.names(head ++ body)), else: []
        bindings = Map.new(names, &{&1, var(&1)})

        with {:ok, params} <- Refusal.map(head, &arith/1),
             {:ok, posted} <-
               Refusal.flat_map(Enum.reject(body, &saying?(&1, said)), &hinted(&1, hints)),
             {:ok, goals} <-
               Refusal.flat_map(Enum.with_index(body), fn {goal, j} ->
                 if saying?(goal, said), do: hinted(goal, hints), else: goals({goal, j}, i, lenp)
               end) do
          {entry, written} = Enum.split_with(goals, &postable?/1)

          {:ok,
           clause(
             method(rname),
             [@self | params ++ lenp ++ [bindings]],
             reading ++ posted ++ goals
           )}
        end

      bad ->
        {:error, {:head_not_a_column, %{head: bad}}}
    end
  end

  @spec saying?(term(), MapSet.t()) :: boolean()
  defp saying?({:call, q, _args}, said), do: MapSet.member?(said, Rel.name(q))
  defp saying?(_goal, _said), do: false

  # The fixpoint narrows from a bound, not from the slack standing for it, so the reading posts.
  @spec hinted(term(), %{atom() => {[term()], String.t()}}) ::
          {:ok, [term()]} | {:error, Refusal.t()}
  defp hinted({:call, q, args}, hints) do
    with {params, al} <- hints[Rel.name(q)],
         {:ok, lowered} <- Refusal.map(args, &arith/1) do
      {:ok, saying(al, Map.new(Enum.zip(params, lowered), fn {{:var, p}, t} -> {var(p), t} end))}
    else
      nil -> {:ok, []}
      error -> error
    end
  end

  defp hinted(_goal, _hints), do: {:ok, []}

  # A reading is AL source over its relation's parameters. Substituted once, so a caller's
  # name of its own cannot be taken for the callee's.
  @spec saying(String.t(), %{AL.Var.t() => term()}) :: [term()]
  defp saying(al, by) do
    {:ok, %AL.Syntax.Result{program: goals}} = AL.Syntax.parse(al <> ".")
    AL.Term.map(goals, &Map.get(by, &1, &1))
  end

  # Structure can bind before its fields. AL carries linear constraints open;
  # nonlinear arithmetic and calls retain their written order.
  @spec postable?(Macro.t()) :: boolean()
  defp postable?({:unify, _, _}), do: true
  defp postable?({:eq, _, [t, u]}), do: linear?(t) and linear?(u)
  defp postable?(_goal), do: false

  @spec linear?(Macro.t()) :: boolean()
  defp linear?({:*, _, [t, u]}),
    do: (is_integer(t) or is_integer(u)) and linear?(t) and linear?(u)

  defp linear?({_op, _, [t, u]}), do: linear?(t) and linear?(u)
  defp linear?(_term), do: true

  # AL's = unifies structure and, wherever arithmetic stands, equates numbers.
  @spec goals({term(), non_neg_integer()}, non_neg_integer(), [term()]) ::
          {:ok, [term()]} | {:error, Refusal.t()}
  defp goals({{:eq, t, u}, j}, i, _lenp) do
    if arithmetic?(t) or arithmetic?(u) do
      with {:ok, goal} <- binary(:eq, t, u), do: {:ok, [goal]}
    else
      with {:ok, defs, [a, b]} <- arguments([t, u], i, j),
           do: {:ok, defs ++ [{:unify, [], [a, b]}]}
    end
  end

  defp goals({{:call, callee, args}, j}, i, lenp) do
    with {:ok, defs, args} <- arguments(args, i, j) do
      witness = v("_B#{i}c#{j}")
      {:ok, defs ++ sent(callee, args ++ lenp ++ [witness], i, j)}
    end
  end

  # A call through a passed name is Prolog's call/N: the compound's arguments lead, send it.
  @spec sent(Term.name() | {:var, atom()}, [term()], non_neg_integer(), non_neg_integer()) ::
          [term()]
  defp sent({:var, carrier}, args, i, j) do
    [nm, ps, as] = for tail <- ~w(Nm Ps As), do: v("_Q#{i}c#{j}#{tail}")

    [
      call(:functor, [var(carrier), nm, ps]),
      call(:concat, [ps, args, as]),
      call(:send, [@self, nm, as])
    ]
  end

  defp sent(name, args, _i, _j), do: [call(method(name), [@self | args])]

  # Calls and equations consume the same values. Only arithmetic needs a fresh result.
  @spec arguments([term()], non_neg_integer(), term()) ::
          {:ok, [Macro.t()], [Macro.t()]} | {:error, Refusal.t()}
  defp arguments(terms, i, j) do
    with {:ok, passed} <- Refusal.map(Enum.with_index(terms), &argument(&1, i, j)) do
      {defs, values} = Enum.unzip(passed)
      {:ok, Enum.concat(defs), values}
    end
  end

  @spec argument({term(), term()}, non_neg_integer(), term()) ::
          {:ok, {[term()], term()}} | {:error, Refusal.t()}
  defp argument({{:papply, name, prefix}, k}, i, j) do
    with {:ok, defs, fixed} <- arguments(prefix, i, "#{j}a#{k}"),
         do: {:ok, {defs, {:{}, [], [method(name), v(:self) | fixed]}}}
  end

  defp argument({{:cons, head, tail}, k}, i, j) do
    with {:ok, defs, [head, tail]} <- arguments([head, tail], i, "#{j}a#{k}"),
         do: {:ok, {defs, [{:|, [], [head, tail]}]}}
  end

  defp argument({term, k}, i, j) do
    fresh = v("_Q#{i}c#{j}a#{k}")

    with {:ok, lifted} <- arith(term) do
      if arithmetic?(term),
        do: {:ok, {[{:eq, [], [fresh, lifted]}], fresh}},
        else: {:ok, {[], lifted}}
    end
  end

  @spec arithmetic?(term()) :: boolean()
  defp arithmetic?(term),
    do:
      term == :len or match?({:reify, _}, term) or
        match?({op, _, _} when op in [:add, :mul], term)

  @spec arith(term()) :: {:ok, term()} | {:error, Refusal.t()}
  defp arith(q) when is_integer(q), do: {:ok, q}
  defp arith(:len), do: {:ok, @len}
  defp arith({:var, nm}), do: {:ok, var(nm)}
  defp arith({:reify, {:eq, t, u}}), do: arith(Ast.arithmetize(Ast.eq(t, u)))
  defp arith({:add, t, u}), do: binary(:+, t, u)
  defp arith({:mul, t, u}), do: binary(:*, t, u)
  defp arith(nil), do: {:ok, []}

  defp arith({:cons, head, tail}) do
    with {:ok, head} <- arith(head),
         {:ok, tail} <- arith(tail),
         do: {:ok, [head | tail]}
  end

  defp arith(term), do: {:error, {:unliftable_term, %{term: term}}}

  @spec binary(atom(), term(), term()) :: {:ok, term()} | {:error, Refusal.t()}
  defp binary(op, t, u) do
    with {:ok, a} <- arith(t),
         {:ok, b} <- arith(u),
         do: {:ok, call(op, [a, b])}
  end

  @spec mentions_len?([{[Term.t()], [Term.goal()]}]) :: boolean()
  defp mentions_len?(clauses) do
    Enum.any?(clauses, fn {head, body} ->
      Term.reduce(head ++ body, false, &(&2 or &1 == :len))
    end)
  end

  @doc "I am the method name a relation is installed under. The prefix keeps relation names from shadowing AL's own methods, such as `concat`."
  @spec method(Term.name()) :: atom()
  def method(name), do: :"rel:#{Rel.name(name)}"

  @spec clause(atom(), [term()], [term()]) :: String.t()
  defp clause(name, head, body),
    do: AL.Syntax.terminate_clause(Printer.defmethod(@ask, name, head, body))

  # The program mints the ask's own object, then defines its methods there.
  @spec installed([String.t()]) :: program()
  defp installed(clauses),
    do: Enum.join([Printer.program([call(:new, [:object, @ask])]) | clauses], "\n\n")

  # Installations share a branch, each on the object its program mints.
  @spec install(program(), AL.Branch.t()) :: {:ok, atom()} | {:error, Refusal.t()}
  defp install(program, branch) do
    with {:ok, bindings} <- run(program, branch, []), do: {:ok, bindings[AL.Var.key(@ask)]}
  end

  @spec run(program(), AL.Branch.t(), keyword()) ::
          {:ok, %{String.t() => term()}} | {:error, Refusal.t()}
  defp run(program, branch, opts) do
    case outcome(AL.run(program, branch, opts)) do
      {:ok, bindings, _state} -> {:ok, bindings}
      {:no, reason} -> {:error, {:send_failed, %{reason: reason}}}
      {:error, _reason} = refusal -> refusal
    end
  end

  @spec landing(term() | nil) :: term()
  defp landing(id) when id in [nil, :head], do: AL.Branch.head().id
  defp landing(id), do: id

  # A surface name is an AL variable once capitalised: x is X, and _s0 stays itself.
  @spec var(atom()) :: AL.Var.t()
  defp var(name), do: name |> Atom.to_string() |> :string.titlecase() |> v()

  @spec query(pos_integer()) :: AL.Var.t()
  defp query(row), do: v("_Qa#{row}")

  @spec v(String.t()) :: AL.Var.t()
  defp v(name), do: AL.Var.var(name)

  @spec call(atom(), [term()]) :: AL.Goal.Compound.t()
  defp call(name, args), do: %AL.Goal.Compound{name: name, args: args}
end
