defmodule Zkfol.Unfold do
  @moduledoc """
  I rewrite a program before it is lowered: I unfold the clauses of every relation the
  root reaches and return what is left of each as a `Clause`.

      p(args)            =>  args = head, body         only one clause of p can match
      p(args)            =>  a walk over p             p steps through root arrays
      r(args)            =>  p(fixed, args)            r was passed as p(fixed)
      array([n], v)      =>  v = [e1, ..., en]         new names for the cells
      nth(q, cells, v)   =>  v = cells[q]              q is a number
      [h | t] = [i | u]  =>  h = i, t = u
      q = r              =>  true or false             both are numbers
      v = t              =>  v replaced by t           v is a name
      n = m + q          =>  m replaced by n - q       m is the only unknown name

  ### Public API

  - `program/2`: the members a root needs, each with its unfolded clauses.
  """

  use TypedStruct

  alias Zkfol.Ast
  alias Zkfol.Lang.{Rel, Term}
  alias Zkfol.Phi.Place

  @depth 64

  @typedoc "A call in a body: the relation and its position among the body's calls to it."
  @type step :: {atom() | nil, non_neg_integer()}

  @typedoc """
  A variable name. Head names stay atoms; any other name carries the calls it was unfolded
  through. Cells of a root array, cells of a walked row and the fixed arguments of a
  passed relation are named after the head name they belong to.
  """
  @type name ::
          atom()
          | {[step()], atom() | non_neg_integer()}
          | {:cell | :row | :captured, atom(), non_neg_integer()}

  @typedoc """
  What a member's parameter is specialised to: a passed relation with n fixed arguments,
  a root array the member walks, or a constant.
  """
  @type handed ::
          nil
          | {:relation, atom(), non_neg_integer()}
          | {:bank, atom(), [non_neg_integer()]}
          | {:fixed, Term.t()}

  @typedoc "A member: a relation and what each of its parameters is specialised to."
  @type key :: {atom(), [handed()]}

  @typedoc """
  Where a call finds its member: through a pointer cell, at the column a walk starts, or
  one column back inside a walk.
  """
  @type at :: :pointer | {:entry, non_neg_integer()} | :back

  typedstruct module: Call, enforce: true do
    @moduledoc "I am a call to a member. `source` is the calls it was unfolded through."
    field(:source, [Zkfol.Unfold.step()])
    field(:member, Zkfol.Unfold.key())
    field(:args, [Zkfol.Lang.Term.t()])
    field(:at, Zkfol.Unfold.at())
  end

  typedstruct module: Primitive, enforce: true do
    @moduledoc "I am a primitive constraint over numbers and lists of cells."
    field(:op, :natural | :nth | :distinct | :permutation)
    field(:args, [Zkfol.Lang.Term.t()])
  end

  typedstruct module: Clause, enforce: true do
    @moduledoc """
    I am an unfolded clause. `banks` are the root arrays it declares and `own_cells` the
    names that need a cell of their own. The lowering reads the calls, then the equations,
    then the primitives.
    """
    field(:head, [Zkfol.Lang.Term.t()])
    field(:banks, %{atom() => [non_neg_integer()]})
    field(:own_cells, [Zkfol.Unfold.name()])
    field(:calls, [Zkfol.Unfold.Call.t()])
    field(:equations, [{Zkfol.Lang.Term.t(), Zkfol.Lang.Term.t()}])
    field(:primitives, [Zkfol.Unfold.Primitive.t()])
  end

  @type program :: [{key(), [Clause.t()]}]

  @typep item ::
           Call.t()
           | Primitive.t()
           | {:eq, Term.t(), Term.t()}
           | {:declared, Term.t(), Term.t(), [non_neg_integer()] | nil}

  @typep env :: %{name() => Term.t()}
  @typep ctx :: %{scope: %{atom() => Rel.t()}, key: key(), root?: boolean()}
  @typep equation :: {Term.t(), Term.t()}

  @doc "I am the members `root` needs, root first, each with its unfolded clauses."
  @spec program(Rel.t(), %{atom() => Rel.t()}) :: program()
  def program(root = %Rel{}, scope),
    do: members([{root.name, List.duplicate(nil, root.arity)}], [], scope)

  @spec members([key()], program(), %{atom() => Rel.t()}) :: program()
  defp members([], done, _scope), do: Enum.reverse(done)

  defp members([key = {name, handed} | queue], done, scope) do
    if List.keymember?(done, key, 0) do
      members(queue, done, scope)
    else
      clauses = scope[name].clauses
      # Only a root with a single clause lays its arrays along the columns.
      ctx = %{scope: scope, key: key, root?: done == [] and length(clauses) == 1}

      unfolded =
        for {head, body} <- clauses,
            do: clause(head, qualify_locals(head, body), head_env(head, handed), ctx)

      called = for %Clause{calls: calls} <- unfolded, %Call{member: member} <- calls, do: member
      members(queue ++ called, [{key, unfolded} | done], scope)
    end
  end

  # Names that are not in the head get an empty path, so only head names are atoms.
  @spec qualify_locals([Term.t()], [Term.goal()]) :: [Term.goal()]
  defp qualify_locals(head, body) do
    heads = Term.names(head)
    rename(body, fn var = {:var, v} -> if v in heads, do: var, else: {:var, {[], v}} end)
  end

  @spec head_env([Term.t()], [handed()]) :: env()
  defp head_env(head, handed) do
    for pair <- Enum.zip(head, handed), reduce: %{} do
      env ->
        case pair do
          {{:var, r}, {:relation, p, n}} ->
            Map.put(env, r, {:papply, p, for(i <- 1..n//1, do: {:var, {:captured, r, i}})})

          {{:var, v}, {:fixed, term}} ->
            Map.put(env, v, term)

          {{:cons, {:var, v}, _rest}, {:bank, _array, inner = [_ | _]}} ->
            Map.put(env, v, bracket(Place.cells(inner, 0, &{:var, {:row, v, &1}})))

          _plain ->
            env
        end
    end
  end

  # I unfold the body until a pass learns nothing new: arrays and numbers found in one
  # pass are known from the start of the next, so a goal can use what is declared after it.
  @spec clause([Term.t()], [Term.goal()], env(), ctx()) :: Clause.t()
  defp clause(head, body, env, ctx) do
    {items, learned} = goals(body, env, [], ctx)

    numbers =
      for {v, term} <- learned, is_integer(resolve({:var, v}, learned)), into: %{}, do: {v, term}

    known =
      for({:declared, value, cells, _dims} <- items, do: {value, cells})
      |> Enum.reduce(env, fn {value, cells}, env -> elem(declare(value, cells, env), 1) end)
      |> Map.merge(numbers)

    if known != env, do: clause(head, body, known, ctx), else: emit(head, items, learned)
  end

  ############################################################
  #                    The Unfolded Clause                   #
  ############################################################

  # A stored name keeps its name and what it is bound to becomes an equation. Any other
  # bound name is replaced by its value.
  @spec emit([Term.t()], [item()], env()) :: Clause.t()
  defp emit(head, items, env) do
    calls = for call = %Call{} <- items, do: call
    primitives = for primitive = %Primitive{} <- items, do: primitive

    unsolved =
      for {:eq, a, b} <- items, resolve(a, env) != resolve(b, env), uniq: true, do: {a, b}

    # A name bound to a sum goes back to being an equation, so `solve_sums/3` can choose
    # which of its names to solve for.
    {sums, env} = Map.split_with(env, &match?({_v, {op, _, _}} when op in [:add, :mul], &1))
    matched = matched(calls, env)
    unsolved = unsolved ++ for({v, sum} <- sums, do: {{:var, v}, sum})
    {env, unsolved} = solve_sums(env, unsolved, matched)

    subst = &substitute(&1, env, matched)
    stored = for {v, term} <- Enum.sort(env), readable?(v, matched), do: {{:var, v}, subst.(term)}
    calls = for call <- calls, do: %{call | args: Enum.map(call.args, subst)}
    equations = for {a, b} <- unsolved, do: {subst.(a), subst.(b)}
    primitives = for prim <- primitives, do: %{prim | args: Enum.map(prim.args, subst)}

    # A number that nothing else places takes a cell of its own.
    numbers =
      Enum.flat_map(primitives, &Term.names(&1.args)) ++
        Enum.flat_map(calls, &summed(&1.args)) ++
        Enum.flat_map(stored ++ equations, &summed(Tuple.to_list(&1)))

    %Clause{
      head: head,
      banks:
        for({:declared, {:var, x}, _cells, dims = [_ | _]} <- items, into: %{}, do: {x, dims}),
      own_cells: numbers |> Enum.uniq() |> Enum.reject(&readable?(&1, matched)),
      calls: calls,
      equations: Enum.sort_by(stored, &equation_order/1) ++ equations,
      primitives: primitives
    }
  end

  # The names a term adds or multiplies.
  @spec summed(term()) :: [name()]
  defp summed({op, a, b}) when op in [:add, :mul], do: Term.names([a, b])
  defp summed(terms) when is_list(terms), do: Enum.flat_map(terms, &summed/1)
  defp summed({:cons, h, t}), do: summed([h, t])
  defp summed({:papply, _p, fixed}), do: summed(fixed)
  defp summed(_leaf), do: []

  # Equations that open a list come first and sums last, so the names inside a list have
  # values before a sum reads them.
  @spec equation_order(equation()) :: 0..2
  defp equation_order({_name, term}) do
    cond do
      Term.reduce(term, false, &(&2 or match?({op, _, _} when op in [:add, :mul], &1))) -> 2
      match?({:cons, _, _}, term) -> 0
      true -> 1
    end
  end

  # The free names the lowering gives a value by matching: the arguments of a pointer
  # call and the elements of a stored name's list.
  @spec matched([Call.t()], env()) :: MapSet.t(name())
  defp matched(calls, env) do
    arguments = for %Call{at: :pointer, args: args} <- calls, arg <- args, do: arg
    lists = for {v, list = {:cons, _, _}} <- env, stored?(v), do: list
    MapSet.new(Enum.flat_map(arguments ++ lists, &pattern_names(&1, env)))
  end

  @spec pattern_names(Term.t(), env()) :: [name()]
  defp pattern_names(var = {:var, _}, env) do
    {:var, r} = root(var, env)

    case env do
      _stored when is_atom(r) or tuple_size(r) == 3 -> []
      %{^r => list = {:cons, _, _}} -> pattern_names(list, env)
      %{^r => _value} -> []
      _free -> [r]
    end
  end

  defp pattern_names({:cons, h, t}, env), do: pattern_names(h, env) ++ pattern_names(t, env)
  defp pattern_names(_other, _env), do: []

  @spec readable?(name(), MapSet.t(name())) :: boolean()
  defp readable?(name, matched), do: stored?(name) or name in matched

  # Head names and the cell, row and captured names have cells of their own.
  @spec stored?(name()) :: boolean()
  defp stored?(name), do: is_atom(name) or tuple_size(name) == 3

  # n = m + q  =>  m = n - q. An equation with exactly one name the lowering cannot read
  # is solved for that name when it is a summand: a guard's slack, or a name defined by a
  # sum.
  @spec solve_sums(env(), [equation()], MapSet.t(name())) :: {env(), [equation()]}
  defp solve_sums(env, equations, matched) do
    subst = &substitute(&1, env, matched)

    solved =
      Enum.find_value(equations, fn equation = {a, b} ->
        {a, b} = {subst.(a), subst.(b)}
        with {m, v} <- solve_sum(a, b, matched) || solve_sum(b, a, matched), do: {equation, m, v}
      end)

    case solved do
      {equation, m, v} -> solve_sums(Map.put(env, m, v), equations -- [equation], matched)
      nil -> {env, equations}
    end
  end

  @spec solve_sum(Term.t(), Term.t(), MapSet.t(name())) :: {name(), Term.t()} | nil
  defp solve_sum(sum, other, matched) do
    summands = summands(sum)

    with [m] <- Enum.reject(Term.names([sum, other]), &readable?(&1, matched)),
         true <- {:var, m} in summands do
      {m, Ast.sub(other, Enum.reduce(summands -- [{:var, m}], 0, &Ast.add(&2, &1)))}
    else
      _other -> nil
    end
  end

  @spec summands(Term.t()) :: [Term.t()]
  defp summands({:add, a, b}), do: summands(a) ++ summands(b)
  defp summands(term), do: [term]

  # Every bound name is replaced by its value, except the names the lowering reads.
  @spec substitute(Term.t(), env(), MapSet.t(name())) :: Term.t()
  defp substitute(var = {:var, _}, env, matched) do
    {:var, r} = root(var, env)

    if is_map_key(env, r) and not readable?(r, matched),
      do: substitute(env[r], env, matched),
      else: {:var, r}
  end

  defp substitute({op, a, b}, env, matched) when op in [:add, :mul],
    do: apply(Ast, op, [substitute(a, env, matched), substitute(b, env, matched)])

  defp substitute({:cons, h, t}, env, matched),
    do: {:cons, substitute(h, env, matched), substitute(t, env, matched)}

  defp substitute({:papply, p, fixed}, env, matched),
    do: {:papply, p, Enum.map(fixed, &substitute(&1, env, matched))}

  defp substitute(term, _env, _matched), do: term

  ############################################################
  #                          Goals                           #
  ############################################################

  # The body's equations are unified first, so they apply whatever order they are in.
  @spec goals([Term.goal()], env(), [step()], ctx()) :: {[item()], env()}
  defp goals(goals, env, path, ctx) do
    env = for {:eq, a, b} <- goals, reduce: env, do: (env -> unify(a, b, env) || env)

    {items, env, _called} =
      Enum.reduce(goals, {[], env, []}, fn goal, {items, env, called} ->
        {more, env, called} = goal(goal, env, called, path, ctx)
        {Enum.reverse(more, items), env, called}
      end)

    {Enum.reverse(items), env}
  end

  # `called` is the relations the body has called so far: a call's step is its relation and
  # its position among the calls to it.
  @spec goal(Term.goal(), env(), [atom()], [step()], ctx()) :: {[item()], env(), [atom()]}
  defp goal({:eq, a, b}, env, called, _path, _ctx) do
    {items, env} = equate(a, b, env)
    {items, env, called}
  end

  defp goal({:call, q, args}, env, called, path, ctx) do
    {rel, args} = callee(q, args, env, ctx)
    step = {rel.name, Enum.count(called, &(&1 == rel.name))}
    {items, env} = call(rel, args, env, path ++ [step], ctx)
    {items, env, [rel.name | called]}
  end

  # An equation that cannot hold becomes `0 = 1`, which makes the clause dead.
  @spec equate(Term.t(), Term.t(), env()) :: {[item()], env()}
  defp equate(a, b, env) do
    case unify(a, b, env) do
      nil -> {[{:eq, 0, 1}], env}
      env -> {[{:eq, a, b}], env}
    end
  end

  @spec callee(term(), [Term.t()], env(), ctx()) :: {Rel.t(), [Term.t()]}
  defp callee(q, args, env, ctx) do
    case resolve(q, env) do
      {:papply, p, fixed} -> {Map.fetch!(ctx.scope, p), fixed ++ args}
      {:var, _unbound} -> throw({:refused, {:unbound_variable, %{goals: [{:call, q, args}]}}})
      named -> {Map.fetch!(ctx.scope, named), args}
    end
  end

  @spec call(Rel.t(), [Term.t()], env(), [step()], ctx()) :: {[item()], env()}
  defp call(rel, args, env, path, ctx) do
    case primitive(rel, args, env) || array(rel, args, env, path, ctx) do
      nil -> relation_call(rel, args, env, path, ctx)
      {:eq, a, b} -> equate(a, b, env)
      {items, env} -> {items, env}
      primitive -> {[primitive], env}
    end
  end

  ############################################################
  #                         Primitives                       #
  ############################################################

  # array(dims, v) with numbers for dims binds v to new cell names. On a head name of the
  # root the array is laid along the columns and its cells are named after that head name.
  @spec array(Rel.t(), [Term.t()], env(), [step()], ctx()) :: {[item()], env()} | nil
  defp array(%Rel{phi: {Zkfol.Array, :array}}, [dims, v], env, path, ctx) do
    sizes = elements(resolve(dims, env), %{})

    if sizes != nil and Enum.all?(sizes, &(is_integer(&1) and &1 >= 0)) do
      value = root(v, env)
      root? = ctx.root? and sizes != [] and match?({:var, x} when is_atom(x), value)
      cell = if root?, do: &{:cell, elem(value, 1), &1}, else: &{path, &1}
      cells = bracket(Place.cells(sizes, 0, &{:var, cell.(&1)}))
      {equations, env} = declare(value, cells, env)
      {[{:declared, value, cells, if(root?, do: sizes)} | equations], env}
    end
  end

  defp array(_rel, _args, _env, _path, _ctx), do: nil

  # The array's name is bound to the cells, and what it was bound to before is unified
  # with them.
  @spec declare(Term.t(), Term.t(), env()) :: {[item()], env()}
  defp declare({:var, r}, cells = {:cons, _, _}, env) do
    case env do
      %{^r => ^cells} -> {[], env}
      %{^r => held} -> equate(held, cells, Map.put(env, r, cells))
      _free -> {[], Map.put(env, r, cells)}
    end
  end

  defp declare(value, cells, env), do: equate(value, cells, env)

  # nil when the relation's clauses have to be used.
  @spec primitive(Rel.t(), [Term.t()], env()) ::
          Primitive.t() | {:eq, Term.t(), Term.t()} | nil
  defp primitive(%Rel{phi: {Ast, :natural}}, [x], _env), do: %Primitive{op: :natural, args: [x]}

  defp primitive(%Rel{phi: {Ast, :nth}}, [i, list, v], env) do
    cells = elements(list, env)
    index = resolve(i, env)

    cond do
      cells == nil or Enum.any?(cells, &Term.sequence?(resolve(&1, env))) -> nil
      index in 1..length(cells)//1 -> {:eq, v, Enum.at(cells, index - 1)}
      true -> %Primitive{op: :nth, args: [i, bracket(cells), v]}
    end
  end

  defp primitive(rel = %Rel{phi: {Ast, :distinct}}, [list], env), do: lookup(rel, [], list, env)

  defp primitive(rel = %Rel{phi: {Ast, :permutation}}, [n, list], env) do
    case resolve(n, env) do
      count when is_integer(count) -> lookup(rel, [count], list, env)
      _unknown -> nil
    end
  end

  defp primitive(_rel, _args, _env), do: nil

  # A lookup only proves over trace cells: the cells of a root array or of a walked row.
  # Any other list uses the relation's clauses.
  @spec lookup(Rel.t(), [Term.t()], Term.t(), env()) :: Primitive.t() | nil
  defp lookup(%Rel{phi: {Ast, op}}, fixed, list, env) do
    with cells when is_list(cells) <- elements(list, env),
         cells = Enum.map(cells, &substitute(&1, env, MapSet.new())),
         true <- Enum.all?(cells, &match?({:var, {tag, _, _}} when tag in [:cell, :row], &1)) do
      %Primitive{op: op, args: fixed ++ [bracket(cells)]}
    else
      _other -> nil
    end
  end

  @spec bracket(term()) :: Term.t()
  defp bracket(cells) when is_list(cells), do: List.foldr(cells, nil, &{:cons, bracket(&1), &2})
  defp bracket(cell), do: cell

  ############################################################
  #                           Calls                          #
  ############################################################

  # A call continues the walk it is in, starts a walk, is replaced by the body of its
  # only matching clause, or becomes a pointer call to a member.
  @spec relation_call(Rel.t(), [Term.t()], env(), [step()], ctx()) :: {[item()], env()}
  defp relation_call(rel, args, env, path, ctx) do
    {name, handed} = ctx.key

    cond do
      # Only the walker's own clause continues the walk, not a clause unfolded into it.
      rel.name == name and length(path) == 1 and Enum.any?(handed, &match?({:bank, _, _}, &1)) ->
        {[%Call{source: path, member: ctx.key, args: args, at: :back}], env}

      walk = walk(rel, args, env) ->
        {handed, extent} = walk
        {[%Call{source: path, member: {rel.name, handed}, args: args, at: {:entry, extent}}], env}

      true ->
        relation = rel.name

        # When the clause still calls the relation, the call is made instead: the caller
        # would pay for the unfolded steps and for the member.
        with true <- length(path) <= @depth,
             [{equations, body}] <- candidates(rel, args, env, path, ctx),
             {items, unfolded} = goals(equations ++ body, env, path, ctx),
             false <-
               Enum.any?(items, &match?(%Call{member: {^relation, _handed}, at: :pointer}, &1)) do
          {items, unfolded}
        else
          _several_or_recursive ->
            handed =
              for arg <- args do
                case resolve(arg, env) do
                  {:papply, p, fixed} -> {:relation, p, length(fixed)}
                  _value -> nil
                end
              end

            {[%Call{source: path, member: {rel.name, handed}, args: args, at: :pointer}], env}
        end
    end
  end

  # A relation walks when it has an empty base clause and a clause that calls itself
  # once, every parameter either stepping one element down a list or passed on unchanged.
  # A call starts a walk when the stepped arguments are root arrays of one length and
  # the unchanged ones are constants.
  @spec walk(Rel.t(), [Term.t()], env()) :: {[handed()], non_neg_integer()} | nil
  defp walk(%Rel{name: name, clauses: [a, b]}, args, env) do
    Enum.find_value([{a, b}, {b, a}], fn {{head, body}, {base, rest}} ->
      with [] <- rest,
           [again] <- for({:call, ^name, again} <- body, do: again),
           handed = Enum.map(Enum.zip([base, head, again, args]), &walk_argument(&1, env)),
           false <- nil in handed,
           arrays = [_ | _] <- for({{:bank, v, _inner}, n} <- handed, do: {v, n}),
           true <- arrays == Enum.uniq_by(arrays, &elem(&1, 0)),
           [extent] <- arrays |> Enum.map(&elem(&1, 1)) |> Enum.uniq() do
        {Enum.map(handed, &with({array = {:bank, _, _}, _left} <- &1, do: array)), extent}
      else
        _other -> nil
      end
    end)
  end

  defp walk(_rel, _args, _env), do: nil

  # One parameter: its base pattern, its head pattern, what the clause passes to itself,
  # and the caller's argument.
  @spec walk_argument({Term.t(), Term.t(), Term.t(), Term.t()}, env()) ::
          {{:bank, atom(), [non_neg_integer()]}, non_neg_integer()} | {:fixed, Term.t()} | nil
  defp walk_argument({nil, {:cons, _head, {:var, tail}}, {:var, tail}, arg}, env),
    do: root_array(arg, env)

  defp walk_argument({{:var, _}, {:var, name}, {:var, name}, arg}, env) do
    value = resolve(arg, env)
    if fixed?(value), do: {:fixed, value}
  end

  defp walk_argument(_other, _env), do: nil

  @spec fixed?(Term.t()) :: boolean()
  defp fixed?(q) when is_integer(q), do: true
  defp fixed?({:papply, _p, fixed}), do: Enum.all?(fixed, &fixed?/1)
  defp fixed?(_term), do: false

  # The root array a list is, or is the rest of, and how many elements are left. The
  # list must be the array's own cells; an equal list written with other names is not it.
  @spec root_array(Term.t(), env()) ::
          {{:bank, atom(), [non_neg_integer()]}, non_neg_integer()} | nil
  defp root_array(term, env) do
    with left = [first | _] <- elements(term, env),
         [{:cell, array, _i} | _] <- Term.names(first),
         whole = [_ | _] <- elements({:var, array}, env),
         true <- List.starts_with?(Enum.reverse(whole), Enum.reverse(left)) do
      {{:bank, array, dimensions(first)}, length(left)}
    else
      _other -> nil
    end
  end

  @spec dimensions(Term.t()) :: [non_neg_integer()]
  defp dimensions(row = {:cons, first, _rest}),
    do: [length(elements(row, %{})) | dimensions(first)]

  defp dimensions(_cell), do: []

  # nil when the list is not closed.
  @spec elements(Term.t(), env()) :: [Term.t()] | nil
  defp elements({:var, v}, env) when is_map_key(env, v), do: elements(env[v], env)

  defp elements({:cons, h, t}, env),
    do: with(rest when is_list(rest) <- elements(t, env), do: [h | rest])

  defp elements(nil, _env), do: []
  defp elements(_open, _env), do: nil

  # The clauses whose head, equations and guards do not contradict the call.
  @spec candidates(Rel.t(), [Term.t()], env(), [step()], ctx()) :: [
          {[Term.goal()], [Term.goal()]}
        ]
  defp candidates(rel, args, env, path, ctx) do
    qualify = fn {:var, v} -> {:var, {path, v}} end

    for {head, body} <- rel.clauses,
        pairs = Enum.zip(rename(head, qualify), args),
        {equations, body} = bind_head(pairs, [], rename(body, qualify), path),
        consistent?(equations ++ body, env, path, ctx),
        do: {equations, body}
  end

  # A head name is replaced by its argument in the body. Any other head pattern, and a
  # head name that was already replaced, is equated with its argument.
  @spec bind_head([{Term.t(), Term.t()}], [Term.goal()], [Term.goal()], [step()]) ::
          {[Term.goal()], [Term.goal()]}
  defp bind_head([], equations, body, _path), do: {Enum.reverse(equations), body}

  defp bind_head([{{:var, v = {path, _name}}, arg} | rest], equations, body, path) do
    replace = &rename(&1, fn term -> if term == {:var, v}, do: arg, else: term end)
    rest = for {pattern, other} <- rest, do: {replace.(pattern), other}
    bind_head(rest, equations, replace.(body), path)
  end

  defp bind_head([{pattern, arg} | rest], equations, body, path),
    do: bind_head(rest, [{:eq, arg, pattern} | equations], body, path)

  @spec consistent?([Term.goal()], env(), [step()], ctx()) :: boolean()
  defp consistent?(goals, env, path, ctx) do
    goals
    |> Enum.with_index()
    |> Enum.reduce(env, fn
      _goal, nil -> nil
      {{:eq, a, b}, _k}, env -> unify(a, b, env)
      {{:call, q, args}, k}, env -> guard(q, args, env, path ++ [{nil, k}], ctx)
    end) != nil
  end

  # A relation with an `@al` definition is a guard. It is decided here when its
  # arguments are numbers; otherwise it is assumed to hold.
  @spec guard(term(), [Term.t()], env(), [step()], ctx()) :: env() | nil
  defp guard(q, args, env, path, ctx) do
    {rel, args} = callee(q, args, env, ctx)

    case {rel.al, rel.phi, rel.clauses, Enum.map(args, &resolve(&1, env))} do
      {nil, _phi, _clauses, _args} -> env
      {_al, {Ast, :natural}, _clauses, [q]} when is_integer(q) and q < 0 -> nil
      {_al, nil, [_clause], _args} -> if(candidates(rel, args, env, path, ctx) != [], do: env)
      _unknown -> env
    end
  end

  @spec rename(term(), (Term.t() -> Term.t())) :: term()
  defp rename({:var, _} = var, fun), do: fun.(var)

  defp rename({tag, a, b}, fun) when tag in [:eq, :add, :mul, :cons],
    do: {tag, rename(a, fun), rename(b, fun)}

  defp rename({:call, q, args}, fun), do: {:call, rename(q, fun), rename(args, fun)}
  defp rename({:papply, p, args}, fun), do: {:papply, p, rename(args, fun)}
  defp rename(terms, fun) when is_list(terms), do: Enum.map(terms, &rename(&1, fun))
  defp rename(leaf, _fun), do: leaf

  ############################################################
  #                        Unification                       #
  ############################################################

  # Bound names are replaced by their values and constants folded.
  @spec resolve(Term.t(), env()) :: Term.t()
  defp resolve({:var, v}, env) when is_map_key(env, v), do: resolve(env[v], env)
  defp resolve({:add, a, b}, env), do: Ast.add(resolve(a, env), resolve(b, env))
  defp resolve({:mul, a, b}, env), do: Ast.mul(resolve(a, env), resolve(b, env))
  defp resolve({:cons, h, t}, env), do: {:cons, resolve(h, env), resolve(t, env)}
  defp resolve({:papply, p, fixed}, env), do: {:papply, p, Enum.map(fixed, &resolve(&1, env))}
  defp resolve(term, _env), do: term

  # `resolve/2` at the top of the term only: a list keeps its elements as written.
  @spec deref(Term.t(), env()) :: Term.t()
  defp deref({:var, v}, env) when is_map_key(env, v), do: deref(env[v], env)
  defp deref(sum = {op, _, _}, env) when op in [:add, :mul], do: resolve(sum, env)
  defp deref(term, _env), do: term

  # The last name of a chain of names bound to names.
  @spec root(Term.t(), env()) :: Term.t()
  defp root(var = {:var, v}, env) do
    case env do
      %{^v => next = {:var, _}} -> root(next, env)
      _value_or_free -> var
    end
  end

  defp root(term, _env), do: term

  # nil when the two cannot be equal.
  @spec unify(Term.t(), Term.t(), env()) :: env() | nil
  defp unify(a, b, env) do
    case {deref(a, env), deref(b, env)} do
      {same, same} ->
        env

      {{:var, v}, {:var, w}} ->
        if rank(v) > rank(w), do: Map.put(env, w, {:var, v}), else: Map.put(env, v, {:var, w})

      {{:var, v}, _value} ->
        bind(v, root(b, env), env)

      {_value, {:var, w}} ->
        bind(w, root(a, env), env)

      {{:cons, h, t}, {:cons, i, u}} ->
        with env = %{} <- unify(h, i, env), do: unify(t, u, env)

      {{:add, {:var, v}, q}, r} when is_integer(q) and is_integer(r) ->
        Map.put(env, v, r - q)

      {r, {:add, {:var, v}, q}} when is_integer(q) and is_integer(r) ->
        Map.put(env, v, r - q)

      {x, y} ->
        if clash?(x, y), do: nil, else: env
    end
  end

  # Of two names for one value the lower-ranked is bound to the other: a stored name is
  # never replaced by a source name, nor a source name by a cell of an unstored array.
  @spec rank(name()) :: 0..2
  defp rank(name) do
    cond do
      stored?(name) -> 2
      is_atom(elem(name, 1)) -> 1
      true -> 0
    end
  end

  # A free name v takes a value. When the value is held by a lower-ranked name r, v
  # holds it instead and r is bound to v.
  @spec bind(name(), Term.t(), env()) :: env()
  defp bind(v, {:var, r}, env) do
    if rank(v) > rank(r),
      do: env |> Map.put(v, Map.fetch!(env, r)) |> Map.put(r, {:var, v}),
      else: Map.put(env, v, {:var, r})
  end

  defp bind(v, term, env), do: Map.put(env, v, term)

  @spec clash?(Term.t(), Term.t()) :: boolean()
  defp clash?(a, b) when is_integer(a) and is_integer(b), do: true
  defp clash?(a, b), do: shape(a) != nil and shape(b) != nil and shape(a) != shape(b)

  @spec shape(Term.t()) :: :number | :empty | :list | nil
  defp shape(q) when is_integer(q), do: :number
  defp shape(nil), do: :empty
  defp shape({:cons, _, _}), do: :list
  defp shape(_other), do: nil
end
