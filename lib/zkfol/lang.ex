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
    clauses = for form <- lines(block), do: rel_clause(name, aliased(form, __CALLER__))
    arity = clauses |> hd() |> elem(0) |> length()

    quote do
      %Zkfol.Lang.Rel{
        name: unquote(name),
        arity: unquote(arity),
        clauses: unquote(Macro.escape(clauses, unquote: true)),
        home: __MODULE__
      }
    end
  end

  @spec rel_clause(atom(), Macro.t()) :: {[term()], [term()]}
  defp rel_clause(name, {name, _meta, args}) do
    args = anonymous(List.wrap(args))

    case List.last(args) do
      [do: block] ->
        {args |> Enum.drop(-1) |> Enum.map(&term/1), block |> lines() |> goals()}

      _bare ->
        {Enum.map(args, &term/1), []}
    end
  end

  defp rel_clause(name, {other, _meta, _args}),
    do: raise(ArgumentError, "the clause #{other} does not belong to the relation #{name}")

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

  @spec store(Macro.t(), [Macro.t()], Macro.Env.t()) :: Macro.t()
  defp store(head, body, env) do
    {name, _meta, args} = head
    {args, body} = anonymous(aliased({List.wrap(args), body}, env))
    clause = {Enum.map(args, &term/1), goals(body)}

    quote do
      @lang_clauses {unquote(name), unquote(length(args)),
                     unquote(Macro.escape(clause, unquote: true)),
                     Module.delete_attribute(__MODULE__, :phi),
                     Module.delete_attribute(__MODULE__, :al)}
    end
  end

  defmacro __before_compile__(env) do
    grouped =
      env.module
      |> Module.get_attribute(:lang_clauses)
      |> Enum.reverse()
      |> Enum.group_by(fn {name, arity, _clause, _phi, _al} -> {name, arity} end)

    rels =
      Enum.map(grouped, fn {{name, arity}, entries} ->
        clauses = for {_name, _arity, clause, _phi, _al} <- entries, do: clause
        phi = Enum.find_value(entries, fn {_n, _a, _c, phi, _al} -> phi end)
        al = Enum.find_value(entries, fn {_n, _a, _c, _phi, al} -> al end)

        quote do
          def unquote(name)() do
            %Zkfol.Lang.Rel{
              name: unquote(name),
              arity: unquote(arity),
              clauses: unquote(Macro.escape(clauses)),
              home: __MODULE__,
              phi: unquote(Macro.escape(phi)),
              al: unquote(Macro.escape(al))
            }
          end
        end
      end)

    names = grouped |> Map.keys() |> Enum.map(&elem(&1, 0)) |> Enum.uniq()

    program =
      quote do
        @doc "I am the module as a program: `root` first, every other defrel behind it."
        @spec program(atom()) :: [Zkfol.Lang.Rel.t()]
        def program(root) do
          all = for name <- unquote(names), do: apply(__MODULE__, name, [])

          case Enum.split_with(all, &(&1.name == root)) do
            {[rooted], rest} -> [rooted | rest]
            {[], _rest} -> raise ArgumentError, "no defrel #{root} in #{inspect(__MODULE__)}"
          end
        end
      end

    rels ++ [program]
  end

  @spec lines(Macro.t()) :: [Macro.t()]
  defp lines({:__block__, _meta, goals}), do: goals
  defp lines(goal), do: [goal]

  @spec term(Macro.t()) :: term()
  defp term({:^, _meta, [expr]}), do: {:unquote, [], [expr]}
  defp term({:len, _meta, ctx}) when is_atom(ctx), do: :len
  defp term({:reify, _meta, [inner]}), do: {:reify, goal(inner, 0)}
  defp term(q) when is_integer(q), do: q
  defp term(s) when is_binary(s), do: s |> String.to_charlist() |> term()
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
  I am the relations `root` reaches, in call order, each pulled from the list, its module,
  its home, `Zkfol.FOL` or `Zkfol.Prims`, and scoped once.
  """
  @spec reached(Rel.t(), [Rel.t()]) :: {:ok, [Rel.t()]} | {:error, Refusal.t()}
  def reached(root = %Rel{}, rels) do
    with {:ok, reached} <-
           gather([{root.name, root.home, true}], Map.new(rels, &{&1.name, &1}), []) do
      scope = MapSet.new(reached, & &1.name)
      {:ok, for(rel <- reached, do: scoped(rel, scope))}
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
          callee <- Rel.calls(rel) ++ Rel.passes(rel),
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

  @typep wanted :: {atom(), module() | nil, boolean()}

  @spec gather([wanted()], %{atom() => Rel.t()}, [Rel.t()]) ::
          {:ok, [Rel.t()]} | {:error, Refusal.t()}
  defp gather([], _known, seen), do: {:ok, Enum.reverse(seen)}

  defp gather([{name, home, needed?} | rest], known, seen) do
    cond do
      Enum.any?(seen, &(&1.name == name)) ->
        gather(rest, known, seen)

      rel = known[name] || pulled(name, [home, Zkfol.FOL, Zkfol.Prims]) ->
        gather(rest ++ wants(rel), Map.put(known, name, rel), [rel | seen])

      needed? ->
        {:error, {:relation_not_in_scope, %{relation: name}}}

      true ->
        gather(rest, known, seen)
    end
  end

  # A passed name is wanted where it resolves and no relation where it does not.
  @spec wants(Rel.t()) :: [wanted()]
  defp wants(rel = %Rel{home: home}) do
    for {names, needed?} <- [{Rel.calls(rel), true}, {Rel.passes(rel), false}],
        name <- names do
      case name do
        {mod, name} -> {name, mod, needed?}
        name -> {name, home, needed?}
      end
    end
  end

  @spec pulled(atom(), [module() | nil]) :: Rel.t() | nil
  defp pulled(name, sources) do
    Enum.find_value(sources, fn source ->
      source && Code.ensure_loaded?(source) && function_exported?(source, name, 0) &&
        apply(source, name, [])
    end)
  end
end
