defmodule Zkfol.Al do
  @moduledoc """
  I am the AL backend: a statement becomes clauses and runs as written,
  so the derivation is the witness. For derivation, each generated method carries its
  source bindings in one final internal argument; questions leave that argument empty.
  """

  alias Zkfol.Al.Ask
  alias Zkfol.Derivation
  alias Zkfol.Lang
  alias Zkfol.Lang.Rel
  alias Zkfol.Lang.Term
  alias Zkfol.Ast
  alias Zkfol.Refusal
  alias Zkfol.Log
  alias Zkfol.Statement

  @heap 256_000_000

  @typedoc "An emitted AL program: goal structs ready for AL.eval/3."
  @type program :: [struct()]

  @typep bind :: %{optional(pos_integer()) => integer()}

  @typep prep :: %{root: Rel.t(), program: program(), bind: bind(), len?: boolean()}

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
    with {:ok, rels} <- rels(target),
         arguments = padded(arguments, hd(rels).arity),
         branch = %AL.Branch{id: landing(Keyword.get(opts, :branch))},
         {:atomic, class} = :mnesia.transaction(fn -> AL.Command.fresh_id(branch) end),
         {:ok, prep} <- prepared(rels, arguments, class, mode),
         heap = Keyword.get(opts, :heap) || @heap,
         :ok <- install(prep.program, branch, heap) do
      {:ok,
       %Ask{
         rels: rels,
         goal: asking(prep, arguments, class),
         class: class,
         arguments: arguments,
         branch: branch,
         heap: heap,
         len?: prep.len?
       }}
    end
  end

  @doc "I take the ask's next answer, and the ask to step again."
  @spec step(Ask.t()) :: {Ask.outcome(), Ask.t()}
  def step(ask = %Ask{state: nil}), do: answered(AL.eval(ask.goal, nil, ask.branch, []), ask)
  def step(ask = %Ask{state: state}), do: answered(AL.next_solution(state), ask)

  @doc "I retract this ask’s clauses; other installations keep theirs."
  @spec close(Ask.t()) :: :ok | {:error, Refusal.t()}
  def close(%Ask{rels: rels, branch: branch, heap: heap, class: class}) do
    program =
      AL.ast_to_pattern({:__block__, [], retractions(Enum.map(rels, &method(&1.name)), class)})

    install(program, branch, heap)
  end

  @spec answered(term(), Ask.t()) :: {Ask.outcome(), Ask.t()}
  defp answered(evaluated, ask) do
    case outcome(evaluated) do
      {:ok, bindings, state} -> {ground(bindings, ask.arguments), %{ask | state: state}}
      {:no, _reason} -> {:exhausted, ask}
      {:error, _reason} = refusal -> {refusal, ask}
    end
  end

  @spec ground(AL.Var.store(), [Statement.datum() | :_]) ::
          {:ok, [Statement.datum()]} | {:error, Refusal.t()}
  defp ground(bindings, arguments) do
    answer =
      for {argument, row} <- Enum.with_index(arguments, 1) do
        if argument == :_,
          do: bindings |> AL.Var.deref(:"$qa#{row}") |> AL.Var.subst(bindings),
          else: argument
      end

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
  defp rels(%Statement{rels: [root | _rest] = rels}), do: Lang.reached(root, rels)
  defp rels(root = %Rel{}), do: Lang.reached(root, [root])
  defp rels([root = %Rel{} | _rest] = list), do: Lang.reached(root, list)
  defp rels(_none), do: {:error, {:no_relations, %{}}}

  @spec prepared([Rel.t()], [Statement.datum() | :_], atom(), :question | :derivation) ::
          {:ok, prep()} | {:error, Refusal.t()}
  defp prepared([root | _rest] = rels, args, class, mode) do
    len? = Enum.any?(rels, &mentions_len?(&1.clauses))

    with {:ok, program} <-
           question_program(Enum.map(rels, &implementation(&1, mode)), len?, class, mode),
         {:ok, bind} <- bind(Enum.to_list(1..root.arity//1), args),
         :ok <- len_bound(len?, bind),
         do: {:ok, %{root: root, program: program, bind: bind, len?: len?}}
  end

  # A question can use a native definition; a derivation needs the source calls as well.
  @spec implementation(Rel.t(), :question | :derivation) :: Rel.t()
  defp implementation(rel = %Rel{al: {:definition, al}}, :question),
    do: %{rel | al: al, clauses: for({head, _body} <- rel.clauses, do: {head, []})}

  defp implementation(rel = %Rel{al: {:definition, al}}, :derivation), do: %{rel | al: al}
  defp implementation(rel, _mode), do: rel

  # len names the trace, which only a bound count sizes ahead of time.
  @spec len_bound(boolean(), bind()) :: :ok | {:error, Refusal.t()}
  defp len_bound(false, _bind), do: :ok
  defp len_bound(true, bind) when is_map_key(bind, 1), do: :ok
  defp len_bound(true, _bind), do: {:error, {:len_needs_a_bound_count, %{}}}

  # The root call: a bound row's value, a query variable elsewhere, the size last where len asks.
  @spec asking(prep(), [Statement.datum() | :_], atom()) :: program()
  defp asking(%{root: root, bind: bind, len?: len?}, arguments, class) do
    sized = if len?, do: [Map.fetch!(bind, 1)], else: []

    goal =
      {method(root.name), [],
       [class | goal(root.arity, bind, arguments) ++ sized ++ [v(:"$bindings")]]}

    [AL.ast_to_pattern(goal)]
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
           case AL.eval(ask.goal, nil, ask.branch, trace_mode: :derivation_trace) do
             {:atomic, {bindings, state}} ->
               {:atomic, {bindings, Derivation.of(state, names, ask.len?)}}

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

  @spec padded([Statement.datum() | :_], non_neg_integer()) :: [Statement.datum() | :_]
  defp padded(args, arity) when length(args) >= arity, do: args
  defp padded(args, arity), do: args ++ List.duplicate(:_, arity - length(args))

  @spec goal(pos_integer(), bind(), [integer() | atom()]) :: [Macro.t() | integer()]
  defp goal(arity, bind, args) do
    Enum.zip(1..arity//1, Stream.concat(args, Stream.cycle([:_])))
    |> Enum.map(fn
      {_row, a} when is_atom(a) and a != :_ -> v(a)
      {row, _} -> Map.get(bind, row, v(:"qa#{row}"))
    end)
  end

  # A search stopped by the budget never reached a no, so it refuses as itself.
  @spec outcome(term()) ::
          {:ok, AL.Var.store(), term()} | {:no, term()} | {:error, Refusal.t()}
  defp outcome({:atomic, {bindings, state}}), do: {:ok, bindings, state}

  defp outcome({:aborted, %{reason: {:resource_limit_exceeded, n}}}),
    do: {:error, {:unresolved_within_budget, %{reductions: n}}}

  defp outcome({:aborted, reason}), do: {:no, reason}
  defp outcome(exceeded), do: Refusal.from_al(exceeded)

  # An argument past the last row addresses nothing; zipping it away would answer another ask.
  @spec bind([pos_integer()], [integer() | atom()]) :: {:ok, bind()} | {:error, Refusal.t()}
  defp bind(rows, args) when length(args) > length(rows),
    do: {:error, {:arguments_exceed_rows, %{args: length(args), rows: length(rows)}}}

  defp bind(rows, args),
    do: {:ok, rows |> Enum.zip(args) |> Enum.reject(fn {_row, a} -> is_atom(a) end) |> Map.new()}

  @spec question_program([Rel.t()], boolean(), atom(), :question | :derivation) ::
          {:ok, program()} | {:error, Refusal.t()}
  defp question_program(rels, len?, class, mode) do
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
      question_clause(rname, al, clause, i, len?, hints, said, class, mode)
    end)
    |> case do
      {:ok, clauses} -> {:ok, installed(clauses, class)}
      refusal -> refusal
    end
  end

  @spec question_clause(
          atom(),
          Macro.t() | nil,
          {[term()], [term()]},
          non_neg_integer(),
          boolean(),
          %{atom() => {[term()], Macro.t()}},
          MapSet.t(),
          atom(),
          :question | :derivation
        ) :: {:ok, Macro.t()} | {:error, Refusal.t()}
  defp question_clause(rname, al, {head, body}, i, len?, hints, said, class, mode) do
    case Enum.find(head, &(not Term.seatable?(&1))) do
      nil ->
        lenp = if len?, do: [v(:len)], else: []
        reading = if al, do: saying(al, %{}), else: []
        # Bind the bundle in the head so it follows this clause through backtracking.
        names = if mode == :derivation, do: Enum.uniq(Term.names(head ++ body)), else: []
        bindings = {:%{}, [], Enum.map(names, &{&1, v(&1)})}

        with {:ok, params} <- Refusal.map(head, &arith/1),
             {:ok, posted} <-
               Refusal.flat_map(Enum.reject(body, &saying?(&1, said)), &hinted(&1, hints)),
             {:ok, goals} <-
               Refusal.flat_map(Enum.with_index(body), fn {goal, j} ->
                 if saying?(goal, said), do: hinted(goal, hints), else: goals({goal, j}, i, lenp)
               end) do
          {entry, written} = Enum.split_with(goals, &postable?/1)

          {:ok,
           defmethod(
             class,
             method(rname),
             [v(:self) | params ++ lenp ++ [bindings]],
             {:__block__, [], reading ++ posted ++ entry ++ written}
           )}
        end

      bad ->
        {:error, {:head_not_a_column, %{head: bad}}}
    end
  end

  @spec saying?(term(), MapSet.t()) :: boolean()
  defp saying?({:call, q, _args}, said), do: MapSet.member?(said, q)
  defp saying?(_goal, _said), do: false

  # The fixpoint narrows from a bound, not from the slack standing for it, so the reading posts.
  @spec hinted(term(), %{atom() => {[term()], Macro.t()}}) ::
          {:ok, [Macro.t()]} | {:error, Refusal.t()}
  defp hinted({:call, q, args}, hints) when is_map_key(hints, q) do
    {params, al} = hints[q]

    with {:ok, lowered} <- Refusal.map(args, &arith/1),
         do:
           {:ok, saying(al, Map.new(Enum.zip(params, lowered), fn {{:var, p}, t} -> {p, t} end))}
  end

  defp hinted(_goal, _hints), do: {:ok, []}

  # Substituted once, so a caller's name of its own cannot be taken for the callee's.
  @spec saying(Macro.t(), %{atom() => Macro.t()}) :: [Macro.t()]
  defp saying(al, by) do
    filled = Map.new(by, fn {name, term} -> {{:hole, name}, term} end)

    al
    |> Macro.prewalk(fn
      {name, _meta, ctx} when is_atom(name) and is_atom(ctx) ->
        if is_map_key(by, name), do: {:hole, name}, else: {name, [], nil}

      node ->
        node
    end)
    |> Macro.prewalk(&Map.get(filled, &1, &1))
    |> case do
      {:__block__, _, goals} -> goals
      goal -> [goal]
    end
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

  @spec goals({term(), non_neg_integer()}, non_neg_integer(), [Macro.t()]) ::
          {:ok, [Macro.t()]} | {:error, Refusal.t()}
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
      witness = v(:"$bindings#{i}c#{j}")
      {:ok, defs ++ sent(callee, args ++ lenp ++ [witness], i, j)}
    end
  end

  # A call through a passed name is Prolog's call/N: rebuild the term, call_term it.
  @spec sent(atom() | {:var, atom()}, [Macro.t()], non_neg_integer(), non_neg_integer()) ::
          [Macro.t()]
  defp sent({:var, carrier}, args, i, j) do
    [nm, ps, as, g] = for tail <- ~w(nm ps as g), do: v(:"q#{i}c#{j}#{tail}")

    [
      {:functor, [], [v(carrier), nm, ps]},
      {:concat, [], [ps, args, as]},
      {:functor, [], [g, nm, as]},
      {:call_term, [], [g]}
    ]
  end

  defp sent(name, args, _i, _j), do: [{method(name), [], [v(:self) | args]}]

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
          {:ok, {[Macro.t()], Macro.t()}} | {:error, Refusal.t()}
  defp argument({{:papply, name, prefix}, k}, i, j) do
    with {:ok, defs, fixed} <- arguments(prefix, i, "#{j}a#{k}"),
         do: {:ok, {defs, {:{}, [], [method(name), v(:self) | fixed]}}}
  end

  defp argument({{:cons, head, tail}, k}, i, j) do
    with {:ok, defs, [head, tail]} <- arguments([head, tail], i, "#{j}a#{k}"),
         do: {:ok, {defs, [{:|, [], [head, tail]}]}}
  end

  defp argument({term, k}, i, j) do
    fresh = v(:"q#{i}c#{j}a#{k}")

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

  @spec arith(term()) :: {:ok, Macro.t()} | {:error, Refusal.t()}
  defp arith(q) when is_integer(q), do: {:ok, q}
  defp arith(:len), do: {:ok, v(:len)}
  defp arith({:var, nm}), do: {:ok, v(nm)}
  defp arith({:reify, {:eq, t, u}}), do: arith(Ast.arithmetize(Ast.eq(t, u)))
  defp arith({:add, t, u}), do: binary(:+, t, u)
  defp arith({:mul, t, u}), do: binary(:*, t, u)
  defp arith(nil), do: {:ok, []}

  defp arith({:cons, head, tail}) do
    with {:ok, head} <- arith(head),
         {:ok, tail} <- arith(tail),
         do: {:ok, [{:|, [], [head, tail]}]}
  end

  defp arith(term), do: {:error, {:unliftable_term, %{term: term}}}

  @spec binary(atom(), term(), term()) :: {:ok, Macro.t()} | {:error, Refusal.t()}
  defp binary(op, t, u) do
    with {:ok, a} <- arith(t),
         {:ok, b} <- arith(u),
         do: {:ok, {op, [], [a, b]}}
  end

  @spec mentions_len?([{[Term.t()], [Term.goal()]}]) :: boolean()
  defp mentions_len?(clauses) do
    Enum.any?(clauses, fn {head, body} ->
      Term.reduce(head ++ body, false, &(&2 or &1 == :len))
    end)
  end

  @doc "I am the method name a relation is installed under. The prefix keeps relation names from shadowing AL's own methods, such as `concat`."
  @spec method(atom()) :: atom()
  def method(name), do: :"rel:#{name}"

  @spec defmethod(atom(), atom(), [Macro.t()], Macro.t()) :: Macro.t()
  defp defmethod(class, name, head, body), do: {:defmethod, [], [class, name, head, [do: body]]}

  @spec installed([Macro.t()], atom()) :: program()
  defp installed(clauses, class) do
    program =
      quote do
        vm_set_class(unquote(class), :object)
        unquote_splicing(clauses)
      end

    AL.ast_to_pattern(program)
  end

  # A closing ask retracts only methods on its own object. A retracted clause stays as
  # history and the next posted counts past it, so the method goes too: a fresh one
  # numbers its clauses from 0, the seq the derivation reads.
  @spec retractions([atom()], atom()) :: [Macro.t()]
  defp retractions(names, class) do
    Enum.flat_map(names, fn name ->
      [
        quote do
          forall([vm_method(unquote(class), unquote(name), impl), vm_clause(impl, h, _b)]) do
            vm_retract_oapply(impl, h)
          end
        end,
        quote do
          forall([vm_method(unquote(class), unquote(name), impl)]) do
            vm_retract_method(unquote(class), unquote(name), impl)
          end
        end
      ]
    end)
  end

  @spec install(program(), AL.Branch.t(), pos_integer()) :: :ok | {:error, Refusal.t()}
  defp install(program, branch, heap) do
    case outcome(AL.eval(program, nil, branch, heap: heap)) do
      {:ok, _bindings, _state} -> :ok
      {:no, reason} -> {:error, {:send_failed, %{reason: reason}}}
      {:error, _reason} = refusal -> refusal
    end
  end

  # Installations share a branch, each on its own object.
  @spec landing(term() | nil) :: term()
  defp landing(id) when id in [nil, :head], do: AL.Branch.head().id
  defp landing(id), do: id

  @spec v(atom()) :: Macro.t()
  defp v(name), do: {name, [], nil}
end
