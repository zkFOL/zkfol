defmodule Zkfol.Lang do
  @moduledoc """
  I am the relational surface: Prolog-shaped clauses, and the relations a root of them
  reaches.

      defrel fib(1, 1)
      defrel fib(2, 1)

      defrel fib(x, v) do
        fib(x - 1, v1)
        fib(x - 2, v2)
        v = v1 + v2
      end
  """

  alias Zkfol.Refusal
  alias Zkfol.Lang.Rel
  alias Zkfol.Lang.Term

  defmacro __using__(_opts) do
    quote do
      import Zkfol.Lang, only: [defrel: 1, defrel: 2, rel: 2]
      Module.register_attribute(__MODULE__, :lang_clauses, accumulate: true)
      @before_compile Zkfol.Lang
    end
  end

  @doc "I am one clause: a bare head is a fact, a block body conjoins goals."
  defmacro defrel(head), do: store(head, [], __CALLER__)
  defmacro defrel(head, do: block), do: store(head, lines(block), __CALLER__)

  @doc "I build a relation where a function runs, `^` splicing the scope's values in."
  defmacro rel(name, do: block) do
    clauses = for form <- lines(block), do: rel_clause(name, form, __CALLER__)

    quote do
      %Zkfol.Lang.Rel{
        name: unquote(name),
        arity: unquote(clauses |> hd() |> elem(0) |> length()),
        clauses: unquote(Macro.escape(clauses, unquote: true)),
        home: __MODULE__
      }
    end
  end

  @spec rel_clause(atom(), Macro.t(), Macro.Env.t()) :: {[term()], [term()]}
  defp rel_clause(name, {name, _meta, args}, env) do
    case Enum.split(List.wrap(args), -1) do
      {head, [[do: block]]} -> clause(head, lines(block), env)
      _fact -> clause(List.wrap(args), [], env)
    end
  end

  defp rel_clause(name, {other, _meta, _args}, _env),
    do: raise(ArgumentError, "the clause #{other} does not belong to the relation #{name}")

  # The `@phi` and `@al` written above a clause belong to its relation.
  @spec store(Macro.t(), [Macro.t()], Macro.Env.t()) :: Macro.t()
  defp store({name, _meta, args}, body, env) do
    clause = clause(List.wrap(args), body, env)

    quote do
      @lang_clauses {unquote(name), unquote(Macro.escape(clause, unquote: true)),
                     Module.delete_attribute(__MODULE__, :phi),
                     Module.delete_attribute(__MODULE__, :al)}
    end
  end

  defmacro __before_compile__(env) do
    grouped =
      env.module
      |> Module.get_attribute(:lang_clauses)
      |> Enum.reverse()
      |> Enum.group_by(&elem(&1, 0))

    relations =
      quote do
        @doc false
        def __relations__, do: unquote(Map.keys(grouped))
      end

    rels =
      Enum.map(grouped, fn {name, entries} ->
        clauses = for {_name, clause, _phi, _al} <- entries, do: clause

        rel = %Rel{
          name: name,
          arity: clauses |> hd() |> elem(0) |> length(),
          clauses: clauses,
          home: env.module,
          phi: Enum.find_value(entries, &elem(&1, 2)),
          al: Enum.find_value(entries, &elem(&1, 3))
        }

        quote do
          def unquote(name)(), do: unquote(Macro.escape(rel))
        end
      end)

    rels ++ [relations]
  end

  @spec clause([Macro.t()], [Macro.t()], Macro.Env.t()) :: {[term()], [term()]}
  defp clause(head, body, env) do
    {head, body} = anonymous(aliased({head, body}, env))
    {Enum.map(head, &term/1), goals(body)}
  end

  @spec anonymous(Macro.t()) :: Macro.t()
  defp anonymous(ast) do
    {renamed, _n} =
      Macro.prewalk(ast, 0, fn
        {:_, meta, ctx}, n when is_atom(ctx) -> {{:"_gensym#{n}", meta, ctx}, n + 1}
        other, n -> {other, n}
      end)

    renamed
  end

  @spec aliased(Macro.t(), Macro.Env.t()) :: Macro.t()
  defp aliased(ast, env) do
    Macro.prewalk(ast, fn
      {{:., dot, [alias, name]}, meta, args} when is_atom(name) ->
        {{:., dot, [Macro.expand(alias, env), name]}, meta, args}

      node ->
        node
    end)
  end

  @spec lines(Macro.t()) :: [Macro.t()]
  defp lines({:__block__, _meta, goals}), do: goals
  defp lines(goal), do: [goal]

  @spec term(Macro.t()) :: term()
  defp term({:^, _meta, [expr]}), do: {:unquote, [], [expr]}
  defp term({:len, _meta, ctx}) when is_atom(ctx), do: :len
  defp term({:reify, _meta, [inner]}), do: {:reify, goal(inner, 0)}
  defp term(q) when is_integer(q), do: q
  defp term([]), do: nil
  defp term([{:|, _meta, [head, tail]}]), do: {:cons, term(head), term(tail)}
  defp term([head | tail]), do: {:cons, term(head), term(tail)}
  defp term({name, _meta, ctx}) when is_atom(name) and is_atom(ctx), do: {:var, name}
  defp term({:+, _meta, [a, b]}), do: sum(term(a), term(b))
  defp term({:*, _meta, [a, b]}), do: product(term(a), term(b))

  defp term({:**, _meta, [a, q]}) when is_integer(q) and q > 0,
    do: Enum.reduce(2..q//1, term(a), fn _k, acc -> {:mul, acc, term(a)} end)

  defp term({:**, _meta, [_a, e]}),
    do: raise(ArgumentError, "an exponent is a positive integer, not #{Macro.to_string(e)}")

  defp term({:-, _meta, [q]}) when is_integer(q), do: -q
  defp term({:-, _meta, [a]}), do: {:mul, term(a), -1}
  defp term({:-, _meta, [a, b]}) when is_integer(b), do: {:add, term(a), -b}
  defp term({:-, _meta, [a, b]}), do: {:add, term(a), {:mul, term(b), -1}}

  defp term({name, _meta, args}) when is_atom(name) and is_list(args),
    do: {:papply, name, Enum.map(args, &term/1)}

  defp term({{:., _dot, [mod, name]}, _meta, args}) when is_atom(mod) and is_list(args),
    do: {:papply, {mod, name}, Enum.map(args, &term/1)}

  # A constant rides right, so every reader of a sum or product sees one form.
  @spec sum(Term.t(), Term.t()) :: Term.t()
  defp sum(q, t) when is_integer(q) and not is_integer(t), do: {:add, t, q}
  defp sum(t, u), do: {:add, t, u}

  @spec product(Term.t(), Term.t()) :: Term.t()
  defp product(q, t) when is_integer(q) and not is_integer(t), do: {:mul, t, q}
  defp product(t, u), do: {:mul, t, u}

  # The index names the existential a call of the library stands on, one per site.
  @spec goals([Macro.t()]) :: [term()]
  defp goals(body), do: for({form, k} <- Enum.with_index(body), do: goal(form, k))

  @spec goal(Macro.t(), non_neg_integer()) :: term()
  defp goal({:=, _meta, [r, {:mod, _site, [e, m]}]}, k),
    do: {:call, :mod, [term(e), term(m), term(r), hole(:q, k)]}

  defp goal({:=, _meta, [a, b]}, _k), do: {:eq, term(a), term(b)}

  defp goal({op, _meta, [a, b]}, k) when op in [:<, :>, :<=, :>=],
    do: {:call, compares(op), [term(a), term(b), hole(:s, k)]}

  defp goal({:!=, _meta, [a, b]}, k),
    do: {:call, :neq, [term(a), term(b), hole(:s, k)]}

  defp goal({name, _meta, args}, _k) when is_atom(name) and is_list(args),
    do: {:call, name, Enum.map(args, &term/1)}

  defp goal({{:., _dot, [mod, name]}, _meta, args}, _k) when is_atom(mod) and is_list(args),
    do: {:call, {mod, name}, Enum.map(args, &term/1)}

  defp goal(form, _k),
    do: raise(ArgumentError, "a goal is an equation or a call, not #{Macro.to_string(form)}")

  @spec compares(atom()) :: atom()
  defp compares(:>), do: :gt
  defp compares(:<), do: :lt
  defp compares(:>=), do: :gte
  defp compares(:<=), do: :lte

  @spec hole(atom(), non_neg_integer()) :: term()
  defp hole(tag, k), do: {:var, :"_#{tag}#{k}"}

  @doc """
  I am the relations `root` reaches, each pulled from the list, its module, its home,
  `Zkfol.FOL` or `Zkfol.Prims`, and scoped once.

  A name a clause's head does not bind is a relation when one answers to it, and a variable
  otherwise. A call to a name that is neither is refused.
  """
  @spec reached(Rel.t(), [Rel.t()]) :: {:ok, [Rel.t()]} | {:error, Refusal.t()}
  def reached(root = %Rel{}, rels) do
    reached = grow([root], Map.new(rels, &{&1.name, &1}), [])
    scope = MapSet.new(reached, & &1.name)
    scoped = for rel <- reached, do: scoped(rel, scope)

    missing =
      for %Rel{clauses: clauses} <- scoped,
          {_head, body} <- clauses,
          {:call, q, _args} <- nodes(body),
          is_atom(q) and q not in scope,
          do: q

    case missing do
      [] -> {:ok, scoped}
      [name | _] -> {:error, {:relation_not_in_scope, %{relation: name}}}
    end
  end

  @doc """
  I return the recursive relation names in a resolved program.

  Calls and passed relations form a directed graph. A relation is recursive when it
  belongs to a cycle; calling a recursive relation does not itself make a caller recursive.
  """
  @spec recursive([Rel.t()]) :: MapSet.t(atom())
  def recursive(rels) do
    graph = :digraph.new()

    try do
      for rel <- rels, do: :digraph.add_vertex(graph, rel.name)

      for rel <- rels,
          {callee, _home} <- free(rel),
          :digraph.vertex(graph, callee) != false do
        :digraph.add_edge(graph, rel.name, callee)
      end

      graph |> :digraph_utils.cyclic_strong_components() |> List.flatten() |> MapSet.new()
    after
      :digraph.delete(graph)
    end
  end

  @spec scoped(Rel.t(), MapSet.t()) :: Rel.t()
  defp scoped(rel = %Rel{clauses: clauses}, scope) do
    clauses =
      for {head, body} <- clauses do
        bound = MapSet.new(Term.names(head))
        {head, for(goal <- body, do: scoped(goal, bound, scope))}
      end

    %{rel | clauses: clauses}
  end

  @spec scoped(term(), MapSet.t(), MapSet.t()) :: term()
  defp scoped({:call, {_mod, q}, args}, bound, scope), do: scoped({:call, q, args}, bound, scope)

  defp scoped({:call, q, args}, bound, scope) do
    callee = if is_atom(q) and MapSet.member?(bound, q), do: {:var, q}, else: q
    {:call, callee, for(arg <- args, do: scoped(arg, bound, scope))}
  end

  defp scoped({:var, q} = var, bound, scope) do
    if MapSet.member?(scope, q) and not MapSet.member?(bound, q), do: {:papply, q, []}, else: var
  end

  defp scoped({:papply, {_mod, q}, fixed}, bound, scope),
    do: scoped({:papply, q, fixed}, bound, scope)

  defp scoped({:papply, q, fixed}, bound, scope),
    do: {:papply, q, for(arg <- fixed, do: scoped(arg, bound, scope))}

  defp scoped({tag, t, u}, bound, scope) when tag in [:add, :mul, :cons, :eq],
    do: {tag, scoped(t, bound, scope), scoped(u, bound, scope)}

  defp scoped({:reify, goal}, bound, scope), do: {:reify, scoped(goal, bound, scope)}
  defp scoped(leaf, _bound, _scope), do: leaf

  # Breadth first from the root, each relation adding those its free names answer to.
  @spec grow([Rel.t()], %{atom() => Rel.t()}, [Rel.t()]) :: [Rel.t()]
  defp grow([], _known, seen), do: Enum.reverse(seen)

  defp grow([rel | queue], known, seen) do
    if Enum.any?(seen, &(&1.name == rel.name)) do
      grow(queue, known, seen)
    else
      found =
        for {name, home} <- free(rel),
            found = known[name] || pulled(name, [home, Zkfol.FOL, Zkfol.Prims]),
            do: found

      grow(queue ++ found, known, [rel | seen])
    end
  end

  # The names each clause's body uses and its head does not bind, each with the module a
  # qualified name points to.
  @spec free(Rel.t()) :: [{atom(), module() | nil}]
  defp free(%Rel{home: home, clauses: clauses}) do
    for {head, body} <- clauses,
        bound = MapSet.new(Term.names(head)),
        node <- nodes(body),
        name <- name(node),
        not MapSet.member?(bound, name),
        uniq: true do
      case name do
        {mod, name} -> {name, mod}
        name -> {name, home}
      end
    end
  end

  # A callee, a partial call, or a variable; a callback is the head's variable.
  @spec name(term()) :: [Term.name()]
  defp name({:call, {:var, _callback}, _args}), do: []
  defp name({tag, name, _args}) when tag in [:call, :papply], do: [name]
  defp name({:var, name}), do: [name]
  defp name(_node), do: []

  # Every node of a term, each before its children.
  @spec nodes(term()) :: [term()]
  defp nodes(term), do: term |> Term.reduce([], &[&1 | &2]) |> Enum.reverse()

  # Only a relation the module defines answers, never another function of its name.
  @spec pulled(atom(), [module() | nil]) :: Rel.t() | nil
  defp pulled(name, sources) do
    Enum.find_value(sources, fn source ->
      source && Code.ensure_loaded?(source) && function_exported?(source, :__relations__, 0) &&
        name in source.__relations__() && apply(source, name, [])
    end)
  end
end
