defmodule Zkfol.Phi do
  @moduledoc """
  I compile relations into constraints and an allocation, then fill that allocation
  from an AL derivation.

  Compilation starts by declaring the root's parameters. Each clause matches its
  head, compiles its goals, and records the storage
  those goals require. Parameters read by surviving constraints receive storage;
  parameters that already refer to existing data retain that access.
  Once the clauses are compiled, unresolved outputs receive storage and each clause
  constrains its returned value there. Alternatives
  requiring both scalar and list values share term identities for that parameter.

  `Zkfol.Phi.Traversal` supplies an optional placement plan before ordinary inlining.
  Its planned arrays share rows across iterations; the plan supplies call addresses.
  Other calls expand their clauses in the caller or use a compiled member at an address.
  Ordinary inlining has three outcomes: no viable clause is dead; one viable clause
  joins the caller's worklist; alternatives or accesses that cannot inline leave a
  member call. Missing bindings wait. Probes check eligible facts throughout the body,
  without settling storage or retaining their allocations.
  A depth limit of 64 also leaves a member call, bounding compiler work rather than
  runtime recursion.
  There is no call-graph, inferred-extent or decreasing-size analysis.

  The clause goal `array(dimensions, value)` establishes a finite array shape.
  Matching views reuse their cells. A declared parameter in a single-clause root owns
  a bank. Structural reads wait for declarations and aliases; remaining reads choose
  heap storage when the member's worklist reaches a fixed point. Local declarations
  allocate cells per invocation. There is no separate declaration-discovery phase.
  Matching and transpose share accesses. The AL derivation supplies values through Lay.

  ### Public API

  - `run/2`, `verb/0`: the pipeline pass.
  - `relaid/2`: compile a derived statement and construct its witness.
  - `compile/3`: return the predicate and allocation.
  - `lower/2`: return the predicate with allocated row numbers.
  """

  @behaviour Zkfol.Pipeline

  alias Zkfol.Alloc
  alias Zkfol.Alloc.Source
  alias Zkfol.Alloc.Bank
  alias Zkfol.Alloc.Member
  alias Zkfol.Alloc.Site
  alias Zkfol.Alloc.Slot
  alias Zkfol.Ast
  alias Zkfol.Derivation
  alias Zkfol.Lay
  alias Zkfol.Lang
  alias Zkfol.Lang.Rel
  alias Zkfol.Phi.Value
  alias Zkfol.Phi.Expression
  alias Zkfol.Phi.Place
  alias Zkfol.Phi.Place.Binding

  require Place
  alias Zkfol.Phi.Schedule
  alias Zkfol.Phi.Walk
  alias Zkfol.Phi.Walk.Clause
  alias Zkfol.Refusal
  alias Zkfol.Statement

  @typep value :: Value.t()
  @typep frame :: Value.frame()
  @typep placement :: {atom(), [value()], frame(), Walk.t()}

  @typep ctx :: %{
           scope: %{atom() => Rel.t()},
           depth: non_neg_integer(),
           traversal: Zkfol.Phi.Traversal.t() | nil,
           ancestors: [{Member.t(), [value()]}],
           taken: MapSet.t(),
           member: atom(),
           site: [non_neg_integer() | atom()],
           source: [{atom(), non_neg_integer()}],
           body: [term()]
         }

  @doc "I lay a derived statement; one that has not run passes through."
  @impl Zkfol.Pipeline
  @spec run(Statement.t(), keyword()) :: {:ok, Statement.t()} | {:error, Refusal.t()}
  def run(statement = %Statement{stage: %Derivation{} = derivation}, _opts),
    do: relaid(statement, derivation)

  def run(statement = %Statement{}, _opts), do: {:ok, statement}

  @impl Zkfol.Pipeline
  @spec verb() :: Zkfol.Pipeline.result()
  def verb, do: :lowers

  @doc "I lay the derivation for the statement; lists use heap storage."
  @spec relaid(Statement.t(), Derivation.t()) ::
          {:ok, Statement.t()} | {:error, Refusal.t()}
  def relaid(
        statement = %Statement{rels: [root | _rest] = rels},
        derivation = %Derivation{}
      ) do
    # What the run established of the root itself: the arguments, every hole filled.
    {_name, args} = Derivation.root(derivation, root.name) || {root.name, []}

    with {:ok, pred, alloc, walk} <- lowered(root, rels, args) do
      stage = %Statement.Solved{
        pred: Alloc.link(pred, alloc),
        lay: Lay.of(derivation, alloc),
        lowering: walk
      }

      {:ok, %{statement | stage: stage}}
    end
  end

  @doc "I am the predicate of `root` against `rels`, linked."
  @spec lower(Rel.t(), [Rel.t()]) :: {:ok, Ast.pred()} | {:error, Refusal.t()}
  def lower(root = %Rel{}, rels) do
    case compile(root, rels) do
      {:ok, pred, alloc} -> {:ok, Alloc.link(pred, alloc)}
      x -> x
    end
  end

  @doc """
  I compile `root`. Array goals supply static dimensions; argument values stay private.
  Lists without an array goal use the heap. AL checks array shapes as part of solving.
  """
  @spec compile(Rel.t(), [Rel.t()] | nil, [term()]) ::
          {:ok, Ast.pred(), Alloc.t()} | {:error, Refusal.t()}
  def compile(root = %Rel{}, rels \\ nil, args \\ []) do
    with {:ok, pred, alloc, _walk} <- lowered(root, rels, args), do: {:ok, pred, alloc}
  end

  # Each pattern against its value, in order; `:dead` is a clause that cannot match.
  @spec match([term()], [Expression.symbolic()], Walk.t()) :: Walk.t() | :dead
  defp match([], [], walk), do: walk

  defp match([pattern | patterns], [value | values], walk) do
    with walk = %Walk{} <- unify(pattern, value, walk), do: match(patterns, values, walk)
  end

  @spec lowered(Rel.t(), [Rel.t()] | nil, [term()]) ::
          {:ok, Ast.pred(), Alloc.t(), Walk.t()} | {:error, Refusal.t()}
  defp lowered(root, rels, args) do
    with {:ok, [root | _rest] = reached} <- Lang.reached(root, rels || [root]) do
      compiled(root, Map.new(reached, &{&1.name, &1}), args)
    end
  end

  @spec compiled(Rel.t(), %{atom() => Rel.t()}, [term()]) ::
          {:ok, Ast.pred(), Alloc.t(), Walk.t()} | {:error, Refusal.t()}
  defp compiled(root = %Rel{}, scope, args) do
    ctx = %{
      scope: scope,
      depth: 0,
      traversal: nil,
      ancestors: [],
      taken: MapSet.new(),
      member: nil,
      site: [],
      source: [],
      body: []
    }

    {name, _binds, walk} = compile_member(root, List.duplicate(:fresh, root.arity), ctx, args)

    pred =
      Ast.conj(
        walk.predicates ++
          for(bank = %Bank{} <- walk.members, do: runs(bank))
      )

    {pred, members} = Zkfol.Nodes.lower(pred, walk.members)
    {:ok, pred, Alloc.numbered(members, name), walk}
  catch
    {:refused, refusal} -> {:error, refusal}
  end

  # A bank's presence is one on a single run starting at column two, so a forger cannot
  # shorten a walk by dropping presence in the middle.
  @spec runs(Bank.t()) :: Ast.pred()
  defp runs(%Bank{name: name}) do
    Ast.disj([
      Ast.eq({:cell, {:in, name}}, 0),
      Ast.eq(Ast.at({:in, name}, :x, 1, -1), 1),
      Ast.eq(:x, 2)
    ])
  end

  ############################################################
  #                     Member Compilation                   #
  ############################################################

  # Local rows are numbered after the parameters', by name, so goal order moves nothing.
  @spec compile_member(Rel.t(), [value()], ctx(), [term()]) ::
          {atom(), [value()], Walk.t()}
  defp compile_member(%Rel{} = rel, handed, ctx, inputs \\ []) do
    name = member_name(rel.name, ctx.taken)
    refs = for sym <- parameter_names(rel), do: {name, {:param, sym}}
    traversal = Zkfol.Phi.Traversal.plan(rel, handed)

    initial =
      if traversal,
        do: Zkfol.Phi.Traversal.parameters(traversal, handed, refs),
        else: parameters(rel, handed, refs, inputs)

    member = %Member{
      name: name,
      relation: rel.name,
      steps: traversal && traversal.steps,
      slots: [],
      sites: %{}
    }

    ctx = %{
      ctx
      | taken: Enum.into([name | Walk.banks(initial)], ctx.taken),
        member: name,
        source: [],
        depth: 0,
        traversal: traversal
    }

    {clauses, parameters} = member_clauses(rel, member, refs, initial, ctx, inputs)

    live = for %Clause{compiled: walk = %Walk{}} <- clauses, do: walk
    present = Ast.eq({:cell, {:in, name}}, 1)
    branches = for clause <- live, do: Ast.conj([present | Enum.sort_by(clause.eqs, &inspect/1)])
    {binds, slots, banks} = parameter_slots(parameters)

    sites =
      Map.new(Enum.with_index(clauses), fn
        {%Clause{compiled: %Walk{sites: sites}}, k} ->
          {k, for({_i, site} <- Enum.sort(sites), do: site)}

        {%Clause{compiled: :dead}, k} ->
          {k, []}
      end)

    local = live |> Enum.flat_map(& &1.slots) |> Enum.sort_by(&elem(&1.allocation, 1))
    member = %{member | sites: sites, slots: slots ++ local}
    predicate = Ast.disj([Ast.eq({:cell, {:in, name}}, 0) | branches])

    walk = %Walk{
      members: [member | banks] ++ Enum.flat_map(live, & &1.members),
      predicates: [predicate | Enum.flat_map(live, & &1.predicates)],
      clauses: clauses
    }

    {name, binds, walk}
  end

  @spec member_name(atom(), MapSet.t()) :: atom()
  defp member_name(q, taken),
    do:
      Enum.find(
        [q | for(i <- 2..(MapSet.size(taken) + 2)//1, do: :"#{q}#{i}")],
        &(&1 not in taken)
      )

  ############################################################
  #                   Parameter Allocation                   #
  ############################################################

  # Parameters have ordinary scalar, closure or heap storage.
  defp parameter_names(%Rel{clauses: clauses}) do
    {head, _body} = Enum.max_by(clauses, fn {_head, body} -> length(body) end)

    for {pattern, k} <- Enum.with_index(head) do
      case pattern do
        {:var, name} -> name
        _pattern -> :"a#{k + 1}"
      end
    end
  end

  @spec parameters(Rel.t(), [value()], [Ast.row_ref()], [term()]) ::
          Walk.t()
  defp parameters(rel, handed, refs, inputs) do
    declarations =
      for {{ref, form}, k} <- Enum.with_index(Enum.zip(refs, handed)) do
        list? =
          Enum.any?(rel.clauses, fn {head, _body} -> Lang.Term.sequence?(Enum.at(head, k)) end)

        # Supplied numbers choose owned cells here; matching never sees their values.
        input = Enum.at(inputs, k)
        form = if is_integer(input), do: input, else: form
        Walk.bind(%Walk{}, ref, Place.plain(form, ref, list?))
      end

    Enum.reduce(declarations, %Walk{}, &Walk.merge/2)
  end

  # Join the live clauses' storage requirements before choosing the member's interface.
  # A heap identity can hold scalars too. A retry gives every alternative that same
  # representation; each retry permanently fixes at least one parameter to heap storage.
  @spec member_clauses(Rel.t(), Member.t(), [Ast.row_ref()], Walk.t(), ctx(), [term()]) ::
          {[Clause.t()], [{Ast.row_ref(), Binding.t()}]}
  defp member_clauses(rel, member, refs, initial, ctx, inputs) do
    binds = Enum.map(refs, &Map.get(initial.env, &1, {:fresh, &1}))
    within = %{ctx | ancestors: [{member, binds} | ctx.ancestors]}
    clauses = compile_clauses(rel, member, binds, initial, within)
    clauses = complete_parameters(clauses, refs, initial, inputs)
    live = for %Clause{compiled: walk = %Walk{}} <- clauses, do: walk
    parameters = shared_parameters(refs, [initial | live])

    shared =
      for {ref, binding = %Binding{allocation: {:node, ref}}} <- parameters,
          Enum.any?(live, &(Map.get(&1.parameters, ref, :none) != binding.allocation)),
          do: {ref, binding}

    case shared do
      [] ->
        {clauses, parameters}

      bindings ->
        initial =
          Enum.reduce(bindings, initial, fn {ref, binding}, walk ->
            Walk.bind(walk, ref, binding)
          end)

        member_clauses(rel, member, refs, initial, ctx, inputs)
    end
  end

  # An unused access contributes no storage requirement. A heap requirement dominates
  # a scalar cell. Otherwise keep the incoming access or the first live owner.
  # No declaration means the completed member leaves that argument unconstrained.
  @spec shared_parameters([Ast.row_ref()], [Walk.t()]) :: [{Ast.row_ref(), Binding.t()}]
  defp shared_parameters(refs, walks) do
    for ref <- refs do
      owners = Enum.filter(walks, &(Map.get(&1.parameters, ref, :none) != :none))

      declaration =
        Enum.find(owners, &(&1.parameters[ref] == {:node, ref})) || List.first(owners) ||
          Enum.find(walks, hd(walks), &is_map_key(&1.parameters, ref))

      {ref,
       %Binding{
         value: Map.get(declaration.env, ref, :fresh),
         allocation: Map.get(declaration.parameters, ref, :none)
       }}
    end
  end

  # Finish unresolved outputs; supplied scalar accesses and declared views stay put.
  @spec complete_parameters([Clause.t()], [Ast.row_ref()], Walk.t(), [term()]) ::
          [Clause.t()]
  defp complete_parameters(clauses, refs, initial, inputs) do
    unresolved = Enum.reject(refs, &Map.has_key?(initial.parameters, &1))
    lists = for {ref, value} <- Enum.zip(refs, inputs), is_list(value), into: %{}, do: {ref, true}

    Enum.map(clauses, fn
      clause = %Clause{compiled: walk = %Walk{}} ->
        read = MapSet.new(parameter_reads(walk.eqs ++ walk.predicates))

        bindings =
          for ref <- unresolved,
              Map.get(walk.parameters, ref) in [nil, :none],
              value = Walk.follow(walk, {:fresh, ref}),
              value not in [{:fresh, ref}, {:cell, ref}] or ref in read or
                is_map_key(lists, ref),
              do: {ref, value}

        # Snapshot aliases before assigning either name its own output cell. An alias
        # to an unresolved parameter still needs equality; an untouched parameter does not.
        walk =
          Enum.reduce(bindings, walk, fn {ref, value}, walk ->
            value = Walk.follow(walk, value)

            storage =
              case value do
                {:fresh, source} when is_map_key(lists, source) -> {:node, Ast.cell(source)}
                _resolved -> value
              end

            allocated = Walk.bind(walk, ref, Place.output(storage, ref))
            unify(Walk.fetch(allocated, ref), value, allocated)
          end)

        %{clause | compiled: walk}

      dead ->
        dead
    end)
  end

  # Generated row names contain their producer expressions. Their parameter references
  # are dependencies too; finding them does not require lowering the heap constraints.
  @spec parameter_reads(term()) :: [Ast.row_ref()]
  defp parameter_reads(ref = {_owner, {:param, _name}}), do: [ref]
  defp parameter_reads(value) when is_tuple(value), do: parameter_reads(Tuple.to_list(value))
  defp parameter_reads(values) when is_list(values), do: Enum.flat_map(values, &parameter_reads/1)
  defp parameter_reads(_literal), do: []

  # Slots consume the agreed interface; they make no further placement decisions.
  @spec parameter_slots([{Ast.row_ref(), Binding.t()}]) ::
          {[value()], [Slot.t()], [Bank.t()]}
  defp parameter_slots(bindings) do
    parameters =
      for {{{_name, {:param, sym}}, %Binding{value: access, allocation: allocation}}, k} <-
            Enum.with_index(bindings) do
        {access,
         %Slot{name: sym, allocation: allocation, source: %Source{binding: {:argument, k}}}}
      end

    banks =
      for {%Place.View{dimensions: dimensions}, %Slot{allocation: {:bank, bank, _extent}}} <-
            parameters,
          do: %Bank{
            name: bank,
            depth: max(1, Enum.product(dimensions))
          }

    {binds, slots} = Enum.unzip(parameters)
    {binds, slots, banks}
  end

  ############################################################
  #                     Clause Constraints                   #
  ############################################################

  # Every clause is compiled, the impossible ones kept as `:dead`, so the views can show
  # why a clause failed.
  @spec compile_clauses(Rel.t(), Member.t(), [value()], Walk.t(), ctx()) ::
          [Clause.t()]
  defp compile_clauses(%Rel{clauses: clauses}, %Member{name: name}, binds, seeded, ctx) do
    {walks, _taken} =
      Enum.map_reduce(Enum.with_index(clauses), ctx.taken, fn {{head, body}, k}, taken ->
        matched = match(head, binds, seeded)

        {compiled, taken} =
          with walk = %Walk{} <- matched,
               walk = %Walk{} <-
                 compile_goals(body, walk, %{ctx | site: [k], taken: taken}, :compile) do
            {walk, Enum.into(Alloc.names(walk.members), taken)}
          else
            :dead -> {:dead, taken}
            {:waiting, _names} -> throw({:refused, {:unbound_variable, %{goals: body}}})
          end

        {%Clause{
           member: name,
           head: head,
           body: body,
           accesses: binds,
           before: seeded,
           matched: matched,
           compiled: compiled
         }, taken}
      end)

    walks
  end

  # A goal that needs a binding not yet made waits; the schedule retries it when the
  # binding appears.
  @spec compile_goals([term()], Walk.t(), ctx(), :compile | :probe) ::
          Walk.t() | :dead | Expression.waiting()
  defp compile_goals(goals, walk, ctx, mode) do
    settle =
      case mode do
        :compile -> &settle_storage(&1, &2, ctx.member)
        :probe -> fn _walk, names -> {:waiting, names} end
      end

    Schedule.run(
      goals_at(goals, ctx),
      walk,
      fn {goal, context}, walk ->
        context = %{
          context
          | taken: Enum.into(Walk.banks(walk) ++ Alloc.names(walk.members), context.taken)
        }

        try do
          case compile_goal(goal, walk, context) do
            more = %Walk{} -> if {:eq, 0, 1} in more.eqs, do: :dead, else: more
            result -> result
          end
        catch
          {:waiting, _names} = waiting -> waiting
        end
      end,
      settle
    )
  end

  defp goals_at(goals, ctx) do
    for {goal, k} <- Enum.uniq_by(Enum.with_index(goals), &elem(&1, 0)),
        do: {goal, %{ctx | body: goals, site: [k | ctx.site]}}
  end

  # Let aliases and declarations settle before choosing storage. Structure takes a heap
  # node; scalar cells allocate only if read after folding. A local array gets an identity.
  defp settle_storage(walk, names, owner) do
    more =
      Enum.reduce(names, walk, fn
        {:storage, ref}, acc ->
          Walk.bind(acc, ref, %Binding{value: {:node, Ast.cell(ref)}, allocation: {:node, ref}})

        {:scalar, ref}, acc ->
          if Map.has_key?(acc.env, ref),
            do: acc,
            else: %{acc | env: Map.put(acc.env, ref, Ast.cell(ref))}

        {:array, name}, acc ->
          %{acc | env: Map.put(acc.env, name, {:fresh, {owner, {:own, {name, []}}}})}

        _binding, acc ->
          acc
      end)

    if more.env == walk.env, do: {:waiting, names}, else: more
  end

  @spec compile_goal(term(), Walk.t(), ctx()) :: Schedule.result()
  defp compile_goal({:eq, a, b}, walk, _ctx), do: equate(a, b, walk)

  defp compile_goal({:call, q, args}, walk, ctx) do
    with {:ok, callee, args} <- Expression.callee(q, args, walk, ctx.scope) do
      cond do
        callee.phi -> phi_goal(callee, args, walk, ctx)
        # A relation of no clauses and no phi steers the derivation only; here it is nothing.
        callee.clauses == [] -> walk
        true -> compile_call(callee, args, walk, ctx)
      end
    end
  end

  # Either side may bind the other; when neither can yet, the names both need are reported.
  @spec equate(term(), term(), Walk.t()) :: Walk.t() | :dead | Expression.waiting()
  defp equate(a = {:var, _}, b = {:var, _}, walk), do: unify(a, b, walk)

  defp equate(a, b, walk) do
    with {:waiting, left} <- equation_side(a, b, walk),
         {:waiting, right} <- equation_side(b, a, walk),
         do: {:waiting, Enum.uniq(left ++ right)}
  end

  # A name or a sum can be bound from the other side; a structure is matched value to value.
  defp equation_side(pattern = {op, _a, _b}, other, walk) when op in [:add, :mul] do
    with {:ok, value} <- Expression.resolve(other, walk),
         do: bind_expression(pattern, value, walk)
  end

  defp equation_side(pattern, other, walk) do
    with {:ok, value} <- Expression.resolve(other, walk), do: unify(pattern, value, walk)
  end

  ############################################################
  #                         Calling                          #
  ############################################################

  # The traversal pass owns recognition and placement policy. The compiler only
  # consumes a self-edge or compiles a planned member using its supplied entry address.
  defp compile_call(callee, args, walk, ctx) do
    values = Enum.map(args, &Expression.argument(&1, walk))

    case Zkfol.Phi.Traversal.call(callee, values, ctx.traversal, ctx.site) do
      frame = {:at, _, _, _} ->
        [{member, binds} | _] = ctx.ancestors
        call_constraints(callee, args, {member.name, binds, frame, %Walk{}}, walk, ctx)

      plan = %Zkfol.Phi.Traversal{} ->
        {name, binds, made} = compile_member(callee, values, ctx)
        call_constraints(callee, args, {name, binds, plan.entry, made}, walk, ctx)

      nil ->
        with :residual <- inline_call(callee, args, values, walk, ctx),
             do: compile_member_call(callee, args, values, walk, ctx)
    end
  end

  # No viable clause is dead; one representable clause expands onto the shared worklist;
  # other calls remain residual. Unknown head structure waits. The limit bounds compiler work.
  @spec inline_call(Rel.t(), [term()], [value()], Walk.t(), ctx()) ::
          Schedule.Expansion.t() | :dead | :residual
  defp inline_call(_callee, _args, _values, _walk, %{depth: depth}) when depth >= 64,
    do: :residual

  defp inline_call(callee, args, values, walk, ctx) do
    arguments =
      Enum.zip_with(args, values, fn arg, value ->
        if value == :fresh, do: Expression.substitute(arg, walk), else: value
      end)

    candidates =
      for {{head, body}, k} <- Enum.with_index(callee.clauses),
          candidate = match_clause(callee.name, k, head, body, arguments, walk, ctx),
          candidate != :dead,
          do: candidate

    case candidates do
      [] -> :dead
      [{body, bound, within}] -> %Schedule.Expansion{goals: goals_at(body, within), walk: bound}
      _alternatives -> :residual
    end
  end

  defp match_clause(name, k, head, body, args, caller, ctx) do
    scope = [k, name | ctx.site]
    source = [{name, occurrence(name, caller, ctx)} | ctx.source]
    within = %{ctx | site: scope, source: source, depth: ctx.depth + 1}
    body = Expression.scoped(body, scope)
    facts = Enum.filter(body, &probe_goal?(&1, ctx.scope))

    with bound = %Walk{} <- match(Expression.scoped(head, scope), args, caller),
         result when result != :dead <- compile_goals(facts, bound, within, :probe) do
      # Facts probe viability and whether these accesses can inline. Unresolved facts
      # leave the candidate viable; a refused access selects ordinary member placement.
      # Compile the chosen body from its head bindings, preserving goal positions and
      # allocating its local slots once.
      {body, bound, within}
    end
  catch
    {:refused, {reason, _}} when reason in [:unbound_variable, :unliftable_term] -> :residual
  end

  defp probe_goal?({:eq, _, _}, _scope), do: true

  defp probe_goal?({:call, name, _args}, scope) when is_atom(name),
    do: scope[name].al != nil

  defp probe_goal?(_goal, _scope), do: false

  defp compile_member_call(callee, args, values, walk, ctx) do
    member =
      reuse_member(callee, values, ctx) || place_new_member(callee, values, ctx)

    call_constraints(callee, args, member, walk, ctx)
  end

  # The caller gains the member's presence, an equation per argument, and the call site.
  @spec call_constraints(Rel.t(), [term()], placement(), Walk.t(), ctx()) ::
          Walk.t() | :dead
  defp call_constraints(callee, args, {name, binds, frame, made}, caller, %{site: [k | _]} = ctx) do
    present = Ast.eq(Value.frame({:cell, {:in, name}}, frame), 1)

    with walk = %Walk{} <-
           match(
             args,
             for(bind <- binds, do: Value.frame(bind, frame)),
             Walk.constrain(caller, [present])
           ) do
      pointers =
        for {:at, {:cell, ref = {_owner, {:own, {sym, _site}}}}, 1, 0} <- [frame],
            do: %Slot{name: sym, allocation: {:cell, ref}}

      site = %Site{
        callee: name,
        address: frame,
        source: Enum.reverse([{callee.name, occurrence(callee.name, walk, ctx)} | ctx.source])
      }

      %{
        walk
        | members: walk.members ++ made.members,
          predicates: walk.predicates ++ made.predicates,
          eqs: Enum.reverse(made.eqs, walk.eqs),
          sites: walk.sites ++ [{k, site}],
          slots: walk.slots ++ pointers,
          clauses: walk.clauses ++ made.clauses
      }
    end
  end

  @spec occurrence(atom(), Walk.t(), ctx()) :: non_neg_integer()
  defp occurrence(name, walk, %{site: [k | _], body: body}) do
    Enum.count(Enum.take(body, k), fn
      {:call, {:var, _} = callback, _args} ->
        {:rel, called, _fixed} = Expression.resolve!(callback, walk)
        called == name

      {:call, called, _args} ->
        called == name

      _goal ->
        false
    end)
  end

  # Reuse an ancestor only when its parameter representation accepts this call.
  @spec reuse_member(Rel.t(), [value()], ctx()) :: placement() | nil
  defp reuse_member(callee, values, ctx) do
    with {%Member{name: ancestor}, binds} <-
           Enum.find(ctx.ancestors, fn {member, _binds} -> member.relation == callee.name end),
         true <- continues?(values, binds) do
      frame = pointer_to(ancestor, ctx)
      {ancestor, binds, frame, %Walk{}}
    else
      _another -> nil
    end
  end

  # A new member receives its arguments through the call site’s pointer.
  @spec place_new_member(Rel.t(), [value()], ctx()) :: placement()
  defp place_new_member(callee, values, ctx) do
    frame = pointer_to(callee.name, ctx)

    handed = Enum.map(values, &Value.unframe(Value.handed(&1), frame))
    {name, binds, walk} = compile_member(callee, handed, ctx)
    {name, binds, frame, walk}
  end

  # A call continues the member being compiled unless it hands a literal list, a pair
  # built from source, a node, a different passed relation, or a different constant.
  @spec continues?([value()], [value()]) :: boolean()
  defp continues?(values, binds) do
    Enum.all?(Enum.zip(values, binds), fn
      {_value, {:node, _id}} ->
        true

      # A member specialized on a constant continues only with that constant.
      {value, bind} when is_integer(bind) ->
        value == bind

      {cells, _bind} when is_list(cells) ->
        false

      {{:pair, _, _}, _bind} ->
        false

      {:fresh, laid} when Place.is_laid(laid) ->
        match?({:at, :x, m, _a} when m != 0, laid.head)

      {{:node, _id}, _bind} ->
        false

      {{:rel, _p, _fixed} = passed, bind} ->
        bind == passed

      _form ->
        true
    end)
  end

  # A call with no affine frame reads through a pointer cell owned by the call site.
  @spec pointer_to(atom(), ctx()) :: frame()
  defp pointer_to(target, ctx) do
    Ast.address({:cell, {ctx.member, {:own, {:"which #{target}", ctx.site}}}}, 1, 0)
  end

  # A known index selects an element by matching. A private index selects scalar cells
  # by constraints; structured elements use the relation's clauses.
  @spec phi_goal(Rel.t(), [term()], Walk.t(), ctx()) :: Walk.t() | :dead | Expression.waiting()
  defp phi_goal(%Rel{phi: {Zkfol.Array, :array}} = callee, [dims, value], walk, ctx) do
    with {:ok, dims} <- Expression.resolve(dims, walk) do
      array = Zkfol.Array.of(Value.elements(dims))
      previous = Expression.substitute(value, walk)

      if Zkfol.Array.known?(array, Expression.argument(value, walk)),
        do: walk,
        else: array_goal(callee, array, previous, walk, ctx)
    end
  end

  defp phi_goal(callee, args, walk, ctx) do
    {module, op} = callee.phi

    case pick(callee.phi, args, walk) do
      {v, selected} ->
        unify(v, selected, walk)

      :clauses ->
        compile_call(callee, args, walk, ctx)

      nil ->
        {resolved, walk} = prepare(args, walk, ctx)

        pred = apply(module, op, resolved) |> Ast.postwalk(&Value.scalar/1)
        Walk.constrain(walk, Ast.folded(pred))
    end
  catch
    # When the phi lowering cannot read a term, the relation's clauses compile the call
    # instead, provided they have a body.
    {:refused, {:unliftable_term, %{term: {:node, _id} = term}}} ->
      if Enum.any?(callee.clauses, fn {_head, body} -> body != [] end),
        do: compile_call(callee, args, walk, ctx),
        else: throw({:refused, {:unliftable_term, %{term: term, relation: callee.name}}})

    {:refused, {:unliftable_term, %{term: {:fresh, ref}}}} ->
      {:waiting, [{:storage, ref}]}

    {:refused, {reason, detail}} ->
      case {reason, Expression.dependencies(args, walk)} do
        {:unliftable_term, [_ | _] = names} -> {:waiting, names}
        _refusal -> throw({:refused, {reason, Map.put(detail, :relation, callee.name)}})
      end
  end

  # Fresh root arrays own banks; existing accesses and local calls retain their storage.
  defp array_goal(callee, array, value, walk, ctx) do
    with {:fresh, ref = {owner, {:param, _}}} <- value,
         [{%Member{name: ^owner, relation: relation}, _binds}] <- ctx.ancestors,
         %Rel{clauses: [_clause]} <- ctx.scope[relation] do
      Walk.merge(Zkfol.Array.bind(array, ref), walk)
    else
      {:var, name} -> {:waiting, [{:array, name}]}
      _local_or_bound -> array_local(callee, array, value, walk, ctx)
    end
  end

  defp array_local(callee, array, value, walk, ctx) do
    source = %Source{
      calls: Enum.reverse([{callee.name, occurrence(callee.name, walk, ctx)} | ctx.source]),
      binding: {:argument, 1},
      clause: List.last(ctx.site)
    }

    ref = {ctx.member, {:param, :"array #{inspect(ctx.site)}"}}
    {access, walk} = Zkfol.Array.local(array, ref, source, walk)

    case value do
      {:fresh, ref} -> %{walk | env: Map.put(walk.env, ref, access)}
      _bound_or_local -> unify(value, access, walk)
    end
  end

  # A scalar's source binding supplies its witness, independently of its physical owner.
  # Bind the unresolved name behind aliases so every use sees the same cell.
  @spec prepare([term()], Walk.t(), ctx()) :: {[Value.t()], Walk.t()}
  defp prepare(args, walk, ctx) do
    Enum.map_reduce(args, walk, fn arg, walk ->
      case {arg, Expression.substitute(arg, walk)} do
        {{:var, original}, variable = {:var, name}} ->
          variable_name =
            case original do
              {_scope, name} -> name
              name -> name
            end

          source = %Source{
            calls: Enum.reverse(ctx.source),
            binding: {:variable, variable_name},
            clause: List.last(ctx.site)
          }

          ref = {ctx.member, {:own, {name, ctx.site}}}
          cell = Ast.cell(ref)
          walk = unify(variable, cell, walk)
          slot = %Slot{name: name, allocation: {:cell, ref}, source: source}
          {cell, %{walk | slots: walk.slots ++ [slot]}}

        _bound ->
          {Value.elements(Expression.resolve!(arg, walk)), walk}
      end
    end)
  end

  @spec pick({module(), atom()}, [term()], Walk.t()) :: {term(), value()} | :clauses | nil
  defp pick({Ast, :nth}, [i, xs, v], walk) do
    index = Expression.argument(i, walk)
    cells = Value.elements(Expression.argument(xs, walk))

    cond do
      match?({:fresh, _}, cells) ->
        :clauses

      is_integer(index) and is_list(cells) and index >= 1 and index <= length(cells) ->
        {v, Enum.at(cells, index - 1)}

      is_list(cells) and not Enum.all?(cells, &Place.scalar?/1) ->
        :clauses

      true ->
        nil
    end
  end

  defp pick(_phi, _args, _env), do: nil

  ############################################################
  #                        Unifying                          #
  ############################################################

  @spec unify(term(), Expression.symbolic(), Walk.t()) :: Walk.t() | :dead
  defp unify(value, value, walk), do: walk
  defp unify(_pattern, :fresh, walk), do: walk
  defp unify(:fresh, _value, walk), do: walk

  # Follow either side's existing binding before applying any matching rule.
  # Below this boundary every variable or parameter reference is unresolved.
  defp unify({tag, name}, value, walk = %Walk{env: env})
       when tag in [:var, :fresh] and is_map_key(env, name),
       do: unify(Walk.fetch(walk, name), value, walk)

  defp unify(value, {tag, name}, walk = %Walk{env: env})
       when tag in [:var, :fresh] and is_map_key(env, name),
       do: unify(value, Walk.fetch(walk, name), walk)

  defp unify({:var, v}, value, walk = %Walk{env: env}) do
    value = Expression.substitute(value, walk)

    if v in Lang.Term.names(value),
      do: throw({:refused, {:unbound_variable, %{variable: v}}})

    %{walk | env: Map.put(env, v, value)}
  end

  defp unify(value, variable = {:var, _name}, walk), do: unify(variable, value, walk)

  # Two unresolved parameters become one until a value binds either.
  defp unify(a = {:fresh, _ref}, {:fresh, other}, walk),
    do: %{walk | env: Map.put(walk.env, other, a)}

  # The parameter takes storage for the value, then is matched against it.
  defp unify({:fresh, ref}, value, walk) do
    value = if value == nil, do: [], else: value

    if is_list(value) or Place.is_laid(value) or
         (is_tuple(value) and elem(value, 0) in [:cons, :pair]),
       do: throw({:waiting, [{:storage, ref}]})

    walk = Walk.bind(walk, ref, Place.output(value, ref))
    unify(Walk.fetch(walk, ref), value, walk)
  end

  defp unify(pattern, {:fresh, _ref} = fresh, walk), do: unify(fresh, pattern, walk)

  defp unify({:node, a}, {:node, b}, walk), do: Walk.constrain(walk, [Ast.eq(a, b)])
  defp unify(node = {:node, _id}, other, walk), do: unify(other, node, walk)

  defp unify(laid, {:node, id}, walk) when Place.is_laid(laid),
    do: Walk.constrain(walk, [Ast.eq(elem(Place.node_of(laid), 1), id)])

  defp unify(q, {:node, id}, walk) when is_integer(q),
    do: Walk.constrain(walk, [Ast.eq(Place.read(:value, id), q)])

  defp unify(q, form, walk)
       when is_integer(q) and (form == :x or elem(form, 0) in [:cell, :add, :mul]),
       do: Walk.constrain(walk, pinned(form, q))

  defp unify(q, _value, _walk) when is_integer(q), do: :dead

  defp unify(nil, value, walk), do: unify([], value, walk)

  defp unify([], value, walk), do: Walk.ended(walk, value)

  defp unify({:cons, h, t}, value, walk), do: unify({:pair, h, t}, value, walk)

  defp unify([h | t], value, walk), do: unify({:pair, h, t}, value, walk)

  defp unify({:pair, h, t}, value, walk) do
    with {:ok, vh, vt, walk} <- Walk.peel(walk, value),
         walk = %Walk{} <- unify(h, vh, walk),
         do: unify(t, vt, walk)
  end

  defp unify(pattern = {op, _a, _b}, value, walk) when op in [:add, :mul] do
    case bind_expression(pattern, value, walk) do
      {:waiting, _names} -> throw({:refused, {:unbound_variable, %{equation: pattern}}})
      matched -> matched
    end
  end

  defp unify(pattern = {:papply, _p, _fixed}, value, walk),
    do: unify(Expression.resolve!(pattern, walk), value, walk)

  # Two lists in banks: the same one, or one counted against the other's elements.
  defp unify(a, b, walk) when Place.is_laid(a) and Place.is_laid(b) do
    cond do
      Place.count(b) -> unify(a, Place.elements(b), walk)
      Place.count(a) -> unify(b, Place.elements(a), walk)
      true -> throw({:refused, {:unliftable_term, %{term: b}}})
    end
  end

  defp unify(a, value, walk) when Place.is_laid(a) and is_list(value), do: unify(value, a, walk)
  defp unify(a, value = {:pair, _, _}, walk) when Place.is_laid(a), do: unify(value, a, walk)
  defp unify(a, _value, _walk) when Place.is_laid(a), do: :dead
  # Two passed relations unify when they name the same relation and their fixed arguments unify.
  defp unify({:rel, p, a}, {:rel, p, b}, walk) when length(a) == length(b), do: match(a, b, walk)
  defp unify({:rel, _p, _f}, _value, _walk), do: :dead

  defp unify(a, b, walk), do: equated(a, b, walk)

  defp bind_expression(pattern, value, walk) do
    case Expression.solve(pattern, walk) do
      {:ok, ^pattern} ->
        equated(pattern, value, walk)

      {:ok, bound} ->
        unify(bound, value, walk)

      {:free, name, rest} ->
        %{walk | env: Map.put(walk.env, name, Ast.sub(Value.scalar(value), rest))}

      waiting = {:waiting, _names} ->
        waiting
    end
  end

  @spec equated(value(), value(), Walk.t()) :: Walk.t() | :dead
  defp equated(a, b, walk) do
    cond do
      is_integer(b) ->
        unify(b, a, walk)

      is_list(b) or match?({:pair, _, _}, b) or Place.is_laid(b) or
          match?({:rel, _p, _f}, b) ->
        :dead

      true ->
        Walk.constrain(walk, [Ast.eq(Value.scalar(a), Value.scalar(b))])
    end
  end

  # An integer against the column pins the column; against anything else, that cell.
  @spec pinned(Ast.term_t(), integer()) :: [Ast.pred()]
  defp pinned(form, q) do
    case Place.affine(form) do
      {1, o} -> [Ast.eq(:x, q - o)]
      _cell -> Ast.folded(Ast.eq(Value.scalar(form), q))
    end
  end
end
