defmodule Zkfol.Phi do
  @moduledoc """
  I compile relations into constraints and an allocation, then fill that allocation
  from an AL derivation.

  Compilation starts by identifying recursive relations and declaring the root's
  parameters. Each clause matches its head, compiles its goals, and records the storage
  those goals require. Parameters read by surviving constraints receive storage;
  parameters that already refer to existing data retain that access.
  Once all clauses have contributed their shape observations, unresolved outputs
  receive storage and each clause constrains its returned value there.

  A call either expands its clauses in the caller or uses a compiled member at an
  address. A member represents one compiled relation. Nonrecursive wrappers can expand
  independently of unrolling; recursive expansion follows `Zkfol.Unrolling`'s size rule.
  An expansion with unresolved storage requirements falls back to a member call.

  Input lists provide bank sizes. The derivation supplies values when Lay fills the allocation.

  ### Public API

  - `run/2`, `verb/0`: the pipeline pass.
  - `relaid/3`: compile a derived statement and construct its witness.
  - `compile/4`: return the predicate and allocation.
  - `lower/3`: return the predicate with allocated row numbers.
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
  alias Zkfol.Phi.Layout
  alias Zkfol.Phi.Place

  require Place
  alias Zkfol.Phi.Schedule
  alias Zkfol.Phi.Walk
  alias Zkfol.Phi.Walk.Clause
  alias Zkfol.Refusal
  alias Zkfol.Statement
  alias Zkfol.Unrolling

  @typep value :: Value.t()
  @typep frame :: Value.frame()
  @typep placement :: {atom(), [value()], frame(), Walk.t()}

  @typep ctx :: %{
           scope: %{atom() => Rel.t()},
           recursive: MapSet.t(),
           ancestors: [{Member.t(), [value()]}],
           taken: MapSet.t(),
           member: atom(),
           site: [non_neg_integer() | atom()],
           source: [{atom(), non_neg_integer()}],
           body: [term()],
           inlining: Unrolling.inlining(),
           unrolling: boolean()
         }

  @doc "I lay a derived statement; one that has not run passes through."
  @impl Zkfol.Pipeline
  @spec run(Statement.t(), keyword()) :: {:ok, Statement.t()} | {:error, Refusal.t()}
  def run(statement = %Statement{stage: %Derivation{} = derivation}, opts),
    do: relaid(statement, derivation, opts)

  def run(statement = %Statement{}, _opts), do: {:ok, statement}

  @impl Zkfol.Pipeline
  @spec verb() :: Zkfol.Pipeline.result()
  def verb, do: :lowers

  @doc "I lay the derivation for the statement; `unrolling: false` lays it with every list in the heap."
  @spec relaid(Statement.t(), Derivation.t(), keyword()) ::
          {:ok, Statement.t()} | {:error, Refusal.t()}
  def relaid(
        statement = %Statement{rels: [root | _rest] = rels},
        derivation = %Derivation{},
        opts \\ []
      ) do
    # What the run established of the root itself: the arguments, every hole filled.
    {_name, args} = Derivation.root(derivation, root.name) || {root.name, []}

    with {:ok, pred, alloc, walk} <- lowered(root, rels, args, opts) do
      stage = %Statement.Solved{
        pred: Alloc.link(pred, alloc),
        lay: Lay.of(derivation, alloc),
        lowering: walk
      }

      {:ok, %{statement | stage: stage}}
    end
  end

  @doc "I am the predicate of `root` against `rels`, linked."
  @spec lower(Rel.t(), [Rel.t()], keyword()) :: {:ok, Ast.pred()} | {:error, Refusal.t()}
  def lower(root = %Rel{}, rels, opts \\ []) do
    case compile(root, rels, [], opts) do
      {:ok, pred, alloc} -> {:ok, Alloc.link(pred, alloc)}
      x -> x
    end
  end

  @doc """
  I compile `root` against `rels` to its predicate and allocation; `args` size its banks.
  `unrolling: false` compiles without `Zkfol.Unrolling`: every list in the heap.
  """
  @spec compile(Rel.t(), [Rel.t()] | nil, [term()], keyword()) ::
          {:ok, Ast.pred(), Alloc.t()} | {:error, Refusal.t()}
  def compile(root = %Rel{}, rels \\ nil, args \\ [], opts \\ []) do
    with {:ok, pred, alloc, _walk} <- lowered(root, rels, args, opts), do: {:ok, pred, alloc}
  end

  # Each pattern against its value, in order; `:dead` is a clause that cannot match.
  @spec match([term()], [Expression.symbolic()], Walk.t()) :: Walk.t() | :dead
  defp match([], [], walk), do: walk

  defp match([pattern | patterns], [value | values], walk) do
    with walk = %Walk{} <- unify(pattern, value, walk), do: match(patterns, values, walk)
  end

  @spec lowered(Rel.t(), [Rel.t()] | nil, [term()], keyword()) ::
          {:ok, Ast.pred(), Alloc.t(), Walk.t()} | {:error, Refusal.t()}
  defp lowered(root, rels, args, opts) do
    with {:ok, [root | _rest] = reached} <- Lang.reached(root, rels || [root]) do
      compiled(root, Map.new(reached, &{&1.name, &1}), args, Keyword.get(opts, :unrolling, true))
    end
  end

  @spec compiled(Rel.t(), %{atom() => Rel.t()}, [term()], boolean()) ::
          {:ok, Ast.pred(), Alloc.t(), Walk.t()} | {:error, Refusal.t()}
  defp compiled(root = %Rel{}, scope, args, unrolling) do
    # A handed integer is data (rule 4): its count may place a bank, its value is never
    # written into the predicate.
    handed =
      for k <- 0..(root.arity - 1)//1 do
        case Enum.at(args, k) do
          cells when is_list(cells) -> cells
          q when is_integer(q) -> {:count, q, nil}
          _open -> :fresh
        end
      end

    ctx = %{
      scope: scope,
      recursive: Lang.recursive(Map.values(scope)),
      ancestors: [],
      taken: MapSet.new(),
      member: nil,
      site: [],
      source: [],
      body: [],
      inlining: %{},
      unrolling: unrolling
    }

    column = if unrolling, do: Unrolling.column(root, handed, %{})
    {name, _binds, walk} = compile_member(root, handed, %{}, column, ctx)

    pred =
      Ast.conj(
        walk.predicates ++
          for(bank = %Bank{} <- walk.members, do: runs(bank))
      )

    {pred, members} = Zkfol.Nodes.lower(Value.shaped(pred, walk.shapes), walk.members)
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
  @spec compile_member(Rel.t(), [value()], Place.known(), Unrolling.t() | nil, ctx()) ::
          {atom(), [value()], Walk.t()}
  defp compile_member(%Rel{} = rel, handed, known, column, ctx) do
    name = member_name(rel.name, ctx.taken)
    syms = Layout.params(rel)
    refs = for sym <- syms, do: {name, {:param, sym}}
    initial = parameters(rel, handed, known, ctx.scope, refs, column)
    binds = Enum.map(refs, &Map.get(initial.env, &1, {:fresh, &1}))

    member = %Member{
      name: name,
      relation: rel.name,
      steps: column && column.counter,
      slots: [],
      sites: %{}
    }

    ctx = %{
      ctx
      | ancestors: [{member, binds} | ctx.ancestors],
        taken: Enum.into([name | Walk.banks(initial)], ctx.taken),
        member: name,
        source: []
    }

    clauses = compile_clauses(rel, member, binds, initial, ctx)
    {clauses, shapes} = complete_parameters(clauses, refs, initial)

    live = for %Clause{compiled: walk = %Walk{}} <- clauses, do: walk
    present = Ast.eq({:cell, {:in, name}}, 1)
    branches = for clause <- live, do: Ast.conj([present | Enum.sort_by(clause.eqs, &inspect/1)])
    {binds, slots, banks} = parameter_slots(refs, initial, live, shapes)

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
      clauses: clauses,
      shapes: shapes
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

  # Each parameter is declared before any clause is matched: as the place Unrolling gives
  # it, a new bank declared with its shape, or as its plain place when nothing unrolls.
  @spec parameters(
          Rel.t(),
          [value()],
          Place.known(),
          %{atom() => Rel.t()},
          [Ast.row_ref()],
          Unrolling.t() | nil
        ) :: Walk.t()
  defp parameters(rel, handed, known, scope, refs, column = %Unrolling{}) do
    {shapes, places} = Unrolling.parameters(rel, refs, handed, known, scope, column)

    declarations =
      for {ref, form, place, shape} <- Enum.zip([refs, handed, places, shapes]) do
        if Place.is_laid(place) and not Place.is_laid(form),
          do: Walk.bank(%Walk{}, ref, place, shape),
          else: Walk.bind(%Walk{}, ref, place)
      end

    Enum.reduce(declarations, Walk.refine(%Walk{}, known), &Walk.merge/2)
  end

  defp parameters(rel, handed, known, _scope, refs, nil) do
    declarations =
      for {{ref, form}, k} <- Enum.with_index(Enum.zip(refs, handed)) do
        Walk.bind(%Walk{}, ref, Place.plain(form, ref, Layout.list?(rel.clauses, k)))
      end

    Enum.reduce(declarations, Walk.refine(%Walk{}, known), &Walk.merge/2)
  end

  # Shape observations belong to the shared banks, including observations made in
  # another clause. Finish new outputs after those observations; supplied accesses stay put.
  @spec complete_parameters([Clause.t()], [Ast.row_ref()], Walk.t()) ::
          {[Clause.t()], Place.known()}
  defp complete_parameters(clauses, refs, initial) do
    live = for %Clause{compiled: walk = %Walk{}} <- clauses, do: walk

    shapes =
      Enum.reduce(live, initial, fn walk, known -> Walk.refine(known, walk.shapes) end).shapes

    unresolved = Enum.reject(refs, &Map.has_key?(initial.parameters, &1))

    clauses =
      Enum.map(clauses, fn
        clause = %Clause{compiled: walk = %Walk{}} ->
          walk = Walk.refine(walk, shapes)
          read = MapSet.new(parameter_reads(walk.eqs ++ walk.predicates))

          bindings =
            for ref <- unresolved,
                Map.get(walk.parameters, ref) in [nil, :none],
                value = Walk.follow(walk, {:fresh, ref}),
                value != {:fresh, ref} or ref in read,
                do: {ref, value}

          # Snapshot aliases before assigning either name its own output cell. An alias
          # to an unresolved parameter still needs equality; an untouched parameter does not.
          walk =
            Enum.reduce(bindings, walk, fn {ref, value}, walk ->
              allocated = Walk.allocate(walk, ref, value)
              unify(Walk.fetch(allocated, ref), value, allocated)
            end)

          %{clause | compiled: walk}

        dead ->
          dead
      end)

    {clauses, shapes}
  end

  # Generated row names contain their producer expressions. Their parameter references
  # are dependencies too; finding them does not require lowering the heap constraints.
  @spec parameter_reads(term()) :: [Ast.row_ref()]
  defp parameter_reads(ref = {_owner, {:param, _name}}), do: [ref]
  defp parameter_reads(value) when is_tuple(value), do: parameter_reads(Tuple.to_list(value))
  defp parameter_reads(values) when is_list(values), do: Enum.flat_map(values, &parameter_reads/1)
  defp parameter_reads(_literal), do: []

  # Supplied accesses stay as declared; new outputs use their completed bindings.
  @spec parameter_slots([Ast.row_ref()], Walk.t(), [Walk.t()], Place.known()) ::
          {[value()], [Slot.t()], [Bank.t()]}
  defp parameter_slots(refs, initial, clauses, shapes) do
    parameters =
      for {ref = {_name, {:param, sym}}, k} <- Enum.with_index(refs) do
        declaration = Enum.find([initial | clauses], initial, &is_map_key(&1.parameters, ref))
        allocation = Map.get(declaration.parameters, ref, :none)
        access = Map.get(declaration.env, ref, {:fresh, ref})

        {Value.shaped(access, shapes),
         %Slot{name: sym, allocation: allocation, source: %Source{binding: {:argument, k}}}}
      end

    banks =
      for {_access, %Slot{allocation: {:bank, bank, _address}}} <- parameters,
          do: %Bank{
            name: bank,
            element: Map.get(shapes, {bank, 1}, :unknown),
            depth:
              case shapes[{bank, 1}] do
                {:list, {:at_least, width}, :scalar} -> max(1, width)
                {:list, {0, width}, :scalar} -> max(1, width)
                _shape -> 1
              end
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
               walk = %Walk{} <- compile_goals(body, walk, %{ctx | site: [k], taken: taken}) do
            {walk, Enum.into(Alloc.names(walk.members), taken)}
          else
            :dead -> {:dead, taken}
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
  @spec compile_goals([term()], Walk.t(), ctx()) :: Walk.t() | :dead
  defp compile_goals(goals, walk, ctx) do
    ctx = %{ctx | body: goals}

    Schedule.run(Schedule.new(goals), walk, fn goal, k, walk ->
      goal_context = %{
        ctx
        | site: [k | ctx.site],
          taken: Enum.into(Alloc.names(walk.members), ctx.taken)
      }

      compile_goal(goal, walk, goal_context)
    end)
  end

  @spec compile_goal(term(), Walk.t(), ctx()) :: Walk.t() | :dead | Expression.waiting()
  defp compile_goal({:eq, a, b}, walk, _ctx), do: equate(a, b, walk)

  defp compile_goal({:call, q, args}, walk, ctx) do
    {callee, args} =
      case q do
        {:var, _r} ->
          {:rel, p, fixed} = Expression.resolve!(q, walk)
          {ctx.scope[p], fixed ++ args}

        _name ->
          {ctx.scope[q] || throw({:refused, {:relation_not_in_scope, %{relation: q}}}), args}
      end

    cond do
      callee.phi -> phi_goal(callee, args, walk, ctx)
      # A relation of no clauses and no phi steers the derivation only; here it is nothing.
      callee.clauses == [] -> walk
      true -> compile_call(callee, args, walk, ctx)
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
  defp equation_side(pattern, other, walk) do
    case pattern do
      {:var, _name} ->
        with {:ok, value} <- Expression.resolve(other, walk), do: unify(pattern, value, walk)

      {op, _a, _b} when op in [:add, :mul] ->
        with {:ok, value} <- Expression.resolve(other, walk),
             do: bind_expression(pattern, value, walk)

      _structure ->
        with {:ok, pattern} <- Expression.resolve(pattern, walk),
             {:ok, value} <- Expression.resolve(other, walk),
             do: unify(pattern, value, walk)
    end
  end

  ############################################################
  #                         Calling                          #
  ############################################################

  # A single-clause nonrecursive wrapper may keep calls in its body. Other expansions
  # need no callees of their own. Both require local values to have witness producers.
  @spec compile_call(Rel.t(), [term()], Walk.t(), ctx()) :: Walk.t() | :dead
  defp compile_call(callee, args, walk, ctx) do
    # A primitive's clauses read a handed count as the cell it stands in.
    values =
      for arg <- args do
        case Expression.argument(arg, walk) do
          {:count, _q, form} when callee.phi != nil -> form
          value -> value
        end
      end

    # Wrapper substitution is independent of recursive unrolling. Other nonrecursive
    # calls try their clauses; recursive calls obey Unrolling, or remain members.
    {strategy, inlining} =
      cond do
        callee.name not in ctx.recursive and length(callee.clauses) == 1 ->
          {:wrapper, ctx.inlining}

        callee.name not in ctx.recursive ->
          {:inline, ctx.inlining}

        ctx.unrolling ->
          Unrolling.strategy(callee, values, walk.shapes, ctx.inlining)

        true ->
          {:residual, ctx.inlining}
      end

    case strategy do
      :residual ->
        matches =
          for {head, _body} <- callee.clauses,
              do: match(head, values, %Walk{shapes: walk.shapes})

        if Enum.all?(matches, &(&1 == :dead)),
          do: :dead,
          else: compile_member_call(callee, args, values, walk, ctx)

      _expand ->
        inline_call(callee, args, values, walk, ctx, {strategy, inlining})
    end
  end

  # Compile each candidate separately, discard impossible clauses, then select an expansion
  # or a member call. The enclosing context is unchanged when expansion is rejected.
  @spec inline_call(
          Rel.t(),
          [term()],
          [value()],
          Walk.t(),
          ctx(),
          {:inline | :wrapper | :prefer_call, Unrolling.inlining()}
        ) :: Walk.t() | :dead
  defp inline_call(callee, args, values, walk, ctx, {strategy, inlining}) do
    arguments =
      for {arg, value} <- Enum.zip(args, values),
          do: if(value == :fresh, do: Expression.substitute(arg, walk), else: value)

    mode =
      if strategy == :wrapper and not match?({:inline, _}, walk.mode),
        do: {:wrapper, []},
        else: {:inline, []}

    within = %{ctx | inlining: inlining}

    expansions =
      for {{head, body}, k} <- Enum.with_index(callee.clauses) do
        inline_clause(callee.name, {k, head, body}, arguments, walk, within, mode)
      end

    candidates = Enum.reject(expansions, &(&1 == :dead))

    case {strategy, candidates} do
      {_strategy, []} ->
        :dead

      # The current policy prefers a member for a counted list when it can be placed.
      {:prefer_call, [{:constrained, expanded}]} ->
        caller = if match?({:inline, _}, walk.mode), do: %{walk | mode: :member}, else: walk

        try do
          case {walk.mode, compile_member_call(callee, args, values, caller, ctx)} do
            {{:inline, _required}, %Walk{}} -> Walk.require(walk, {:member, callee.name})
            {_mode, placed} -> placed
          end
        catch
          {:refused, {:unliftable_term, _detail}} -> expanded
        end

      {_strategy, [{kind, expanded}]} when kind in [:substitution, :constrained] ->
        expanded

      _residual ->
        compile_member_call(callee, args, values, walk, ctx)
    end
  end

  # A trial records the required member. A wrapper expansion can realize it immediately,
  # continuing a member being laid or making a new one.
  @spec compile_member_call(Rel.t(), [term()], [value()], Walk.t(), ctx()) :: Walk.t() | :dead
  defp compile_member_call(
         callee,
         _args,
         _values,
         walk = %Walk{mode: {:inline, _required}},
         _ctx
       ),
       do: Walk.require(walk, {:member, callee.name})

  defp compile_member_call(callee, args, values, walk, ctx) do
    member =
      reuse_member(callee, values, ctx) || place_new_member(callee, values, walk.shapes, ctx)

    call_constraints(callee, args, member, walk, ctx)
  end

  # Inlined names belong to this call site and remain available throughout the member.
  # The call adds bindings directly; only an expression's consumer resolves those bindings.
  @spec inline_clause(
          atom(),
          {non_neg_integer(), [term()], [term()]},
          [term()],
          Walk.t(),
          ctx(),
          Walk.mode()
        ) ::
          {:substitution | :constrained, Walk.t()} | :dead | :residual
  defp inline_clause(name, {k, head, body}, args, caller, ctx, mode) do
    if length(ctx.site) > 3000, do: throw({:refused, {:unroll_budget, %{relation: name}}})
    scope = [k, name | ctx.site]
    head = scoped(head, scope)
    body = scoped(body, scope)
    source = [{name, occurrence(name, caller, ctx)} | ctx.source]

    with bound = %Walk{} <- match(head, args, %{caller | mode: mode}),
         walk = %Walk{mode: {_, []}} <-
           compile_goals(body, bound, %{ctx | site: scope, source: source}) do
      outputs = for pattern <- head, do: Expression.resolve!(pattern, walk)
      free = walk.eqs == caller.eqs and not Enum.any?(outputs, &arithmetic?/1)
      {if(free, do: :substitution, else: :constrained), %{walk | mode: caller.mode}}
    else
      :dead -> :dead
      _required -> :residual
    end
  catch
    {:refused, {reason, _detail}} when reason in [:unbound_variable, :unliftable_term] ->
      :residual
  end

  defp scoped({:var, name}, scope), do: {:var, {scope, name}}

  defp scoped({op, a, b}, scope) when op in [:eq, :add, :mul, :cons],
    do: {op, scoped(a, scope), scoped(b, scope)}

  defp scoped({:call, q, args}, scope), do: {:call, scoped(q, scope), scoped(args, scope)}
  defp scoped({:papply, q, args}, scope), do: {:papply, q, scoped(args, scope)}
  defp scoped({:reify, goal}, scope), do: {:reify, scoped(goal, scope)}
  defp scoped(terms, scope) when is_list(terms), do: Enum.map(terms, &scoped(&1, scope))
  defp scoped(leaf, _scope), do: leaf

  @spec arithmetic?(value()) :: boolean()
  defp arithmetic?({op, _a, _b}) when op in [:add, :mul], do: true
  defp arithmetic?({:pair, h, t}), do: arithmetic?(h) or arithmetic?(t)
  defp arithmetic?([h | t]), do: arithmetic?(h) or arithmetic?(t)
  defp arithmetic?(_value), do: false

  # The caller gains the member's presence, an equation per argument, and the call site.
  @spec call_constraints(Rel.t(), [term()], placement(), Walk.t(), ctx()) ::
          Walk.t() | :dead
  defp call_constraints(callee, args, {name, binds, frame, made}, caller, %{site: [k | _]} = ctx) do
    caller = Walk.refine(caller, made.shapes)
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

  # Rule 3. A literal list or a different passed relation cannot continue a member.
  @spec reuse_member(Rel.t(), [value()], ctx()) :: placement() | nil
  defp reuse_member(callee, values, ctx) do
    with {%Member{name: ancestor, steps: steps}, binds} <-
           Enum.find(ctx.ancestors, fn {member, _binds} -> member.relation == callee.name end),
         true <- continues?(values, binds) do
      frame = framed_at(if(steps, do: Unrolling.frame(values, steps), else: :ptr), ancestor, ctx)
      {ancestor, binds, frame, %Walk{}}
    else
      _another -> nil
    end
  end

  @spec place_new_member(Rel.t(), [value()], Place.known(), ctx()) :: placement()
  defp place_new_member(callee, values, known, ctx) do
    lifted = for form <- values, do: Value.handed(form)
    column = if ctx.unrolling, do: Unrolling.column(callee, lifted, known)

    frame =
      framed_at(
        if(column, do: Unrolling.frame(values, column.counter), else: :ptr),
        callee.name,
        ctx
      )

    handed = Enum.map(lifted, &Value.unframe(&1, frame))
    {name, binds, walk} = compile_member(callee, handed, known, column, ctx)
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
        match?({m, _a} when m != 0, Place.extent(laid))

      {{:node, _id}, _bind} ->
        false

      {{:rel, _p, _fixed} = passed, bind} ->
        bind == passed

      _form ->
        true
    end)
  end

  # A call with no affine frame reads through a pointer cell owned by the call site.
  @spec framed_at(frame() | :ptr, atom(), ctx()) :: frame()
  defp framed_at(:ptr, target, ctx) do
    Ast.address({:cell, {ctx.member, {:own, {:"which #{target}", ctx.site}}}}, 1, 0)
  end

  defp framed_at(frame, _target, _ctx), do: frame

  # A known index selects an element by matching. A private index selects scalar cells
  # by constraints; structured elements use the relation's clauses.
  @spec phi_goal(Rel.t(), [term()], Walk.t(), ctx()) :: Walk.t() | :dead
  defp phi_goal(callee, args, walk, ctx) do
    {module, op} = callee.phi

    case pick(callee.phi, args, walk) do
      {v, selected} ->
        unify(v, selected, walk)

      :clauses ->
        compile_call(callee, args, walk, ctx)

      nil ->
        {resolved, walk} = prepare(args, walk, ctx)

        Walk.constrain(walk, Ast.folded(apply(module, op, resolved)))
    end
  catch
    # When the phi lowering cannot read a term, the relation's clauses compile the call
    # instead, provided they have a body.
    {:refused, {:unliftable_term, %{term: {:node, _id} = term}}} ->
      if Enum.any?(callee.clauses, fn {_head, body} -> body != [] end),
        do: compile_call(callee, args, walk, ctx),
        else: throw({:refused, {:unliftable_term, %{term: term, relation: callee.name}}})

    {:refused, {reason, detail}} ->
      throw({:refused, {reason, Map.put(detail, :relation, callee.name)}})
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
          {Value.elements(Expression.resolve!(arg, walk), walk.shapes), walk}
      end
    end)
  end

  @spec pick({module(), atom()}, [term()], Walk.t()) :: {term(), value()} | :clauses | nil
  defp pick({Ast, :nth}, [i, xs, v], walk) do
    index = Expression.argument(i, walk)
    cells = Value.elements(Expression.argument(xs, walk), walk.shapes)

    cond do
      is_integer(index) and is_list(cells) and index >= 1 and index <= length(cells) ->
        {v, Enum.at(cells, index - 1)}

      is_list(cells) and Enum.any?(cells, &(Place.shape(&1, walk.shapes) != :scalar)) ->
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

  defp unify({:var, v}, value, walk = %Walk{env: env}) do
    case env do
      %{^v => _held} ->
        unify(Expression.substitute({:var, v}, walk), value, walk)

      _fresh ->
        value = Expression.substitute(value, walk)

        cond do
          value == {:var, v} -> walk
          v in Lang.Term.names(value) -> throw({:refused, {:unbound_variable, %{variable: v}}})
          true -> %{walk | env: Map.put(env, v, value)}
        end
    end
  end

  defp unify(value, variable = {:var, _name}, walk), do: unify(variable, value, walk)

  # Two unresolved parameters become one until a value binds either.
  defp unify(a = {:fresh, ref}, b = {:fresh, other}, walk = %Walk{env: env}) do
    cond do
      is_map_key(env, ref) -> unify(Walk.fetch(walk, ref), b, walk)
      is_map_key(env, other) -> unify(a, Walk.fetch(walk, other), walk)
      true -> %{walk | env: Map.put(env, other, a)}
    end
  end

  # The parameter takes storage for the value, then is matched against it.
  defp unify({:fresh, ref}, value, walk = %Walk{env: env}) do
    case env do
      %{^ref => _bound} ->
        unify(Walk.fetch(walk, ref), value, walk)

      _unbound ->
        value = if value == nil, do: [], else: value
        walk = Walk.allocate(walk, ref, value)
        unify(Walk.fetch(walk, ref), value, walk)
    end
  end

  # A bracket against a parameter nothing placed: the parameter takes a bank of the
  # bracket's length, open past its tail. The layout places what a body binds for the
  # callee's own parameters; a caller's unbound output reaches here.
  defp unify({:cons, _h, _t}, {:fresh, ref}, walk = %Walk{mode: {_, _}, env: env})
       when not is_map_key(env, ref),
       do: Walk.require(walk, {:bank, ref})

  defp unify({:cons, _h, _t} = bracket, {:fresh, ref}, walk = %Walk{env: env})
       when not is_map_key(env, ref) do
    extent =
      case Lang.Term.closed(bracket) do
        nil -> {1, 0}
        elements -> {0, length(elements)}
      end

    shape = {:list, extent, :unknown}
    walk = Walk.bank(walk, ref, {:along, {Bank.of(ref), 1}, Place.head(shape)}, shape)
    unify(bracket, walk.env[ref], walk)
  end

  defp unify(pattern, {:fresh, _ref} = fresh, walk), do: unify(fresh, pattern, walk)

  defp unify({:node, a}, {:node, b}, walk), do: Walk.constrain(walk, [Ast.eq(a, b)])
  defp unify(node = {:node, _id}, other, walk), do: unify(other, node, walk)

  defp unify(laid, {:node, id}, walk) when Place.is_laid(laid),
    do: Walk.constrain(walk, [Ast.eq(elem(Place.node_of(laid), 1), id)])

  defp unify(q, {:node, id}, walk) when is_integer(q),
    do: Walk.constrain(walk, [Ast.eq(Place.read(:value, id), q)])

  defp unify(q, {:count, _held, form}, walk) when is_integer(q),
    do: Walk.constrain(walk, [Ast.eq(form, q)])

  defp unify(q, form, walk)
       when is_integer(q) and (form == :x or elem(form, 0) in [:cell, :add, :mul]),
       do: Walk.constrain(walk, pinned(form, q))

  # An integer against an element: a record has no number, an element still unknown may.
  defp unify(q, element = {:across, row, _address, _skipped}, walk) when is_integer(q) do
    case Map.get(walk.shapes, row) do
      {:list, _extent, _fields} -> :dead
      _scalar_or_unknown -> Walk.constrain(walk, [Ast.eq(element, q)])
    end
  end

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
    known = walk.shapes

    cond do
      a == b -> walk
      Place.count(b) -> unify(a, Place.elements(b, known), walk)
      Place.count(a) -> unify(b, Place.elements(a, known), walk)
      true -> throw({:refused, {:unliftable_term, %{term: b}}})
    end
  end

  defp unify(a, value, walk) when Place.is_laid(a) and is_list(value), do: unify(value, a, walk)
  defp unify(a, value = {:pair, _, _}, walk) when Place.is_laid(a), do: unify(value, a, walk)
  defp unify(a, _value, _walk) when Place.is_laid(a), do: :dead
  # Two passed relations unify when they name the same relation and their fixed arguments unify.
  defp unify({:rel, p, a}, {:rel, p, b}, walk) when length(a) == length(b), do: match(a, b, walk)
  defp unify({:rel, _p, _f}, _value, _walk), do: :dead

  defp unify(element = {:across, _, _, _}, value, walk)
       when is_list(value) or (is_tuple(value) and elem(value, 0) == :pair),
       do: unify(value, element, walk)

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
