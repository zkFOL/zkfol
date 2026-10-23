defmodule Zkfol.Lang do
  @moduledoc """
  I translate relational clauses into data, leaving references to Elixir.

  ### Public API

  - `defrel/1,2`: declare separate clauses of a module's relation constructor.
  - `rel/1`: construct a relation from a block, with `^` inserting Elixir values.

  Calls name constructors; `each(xs, natural())` passes a relation. A head parameter
  `r` is called with `r(x)`.
  A relation's own name refers to itself unless shadowed by a head parameter.
  """

  alias Zkfol.Lang.{Rel, Term}

  defmacro __using__(_opts) do
    quote do
      import Zkfol.Lang, only: [defrel: 1, defrel: 2, rel: 1]
      Module.register_attribute(__MODULE__, :lang_clauses, accumulate: true)
      @before_compile Zkfol.Lang
    end
  end

  @doc "I accumulate one clause, preserving the declaration's Elixir context."
  @spec defrel(Macro.t(), keyword()) :: Macro.t()
  defmacro defrel({name, _, args}, body \\ []) do
    # Pins are values at the declaration; the nested quote retains reference syntax.
    {args, body} =
      Macro.prewalk({args, body}, fn
        {:^, meta, [expr]} ->
          {:^, meta, [{:unquote, [], [quote(do: Macro.escape(unquote(expr)))]}]}

        node ->
          node
      end)

    code = clause(name, List.wrap(args), Keyword.get(body, :do, {:__block__, [], []}))
    quoted = {:quote, [], [[do: code]]}

    quote do
      @lang_clauses {unquote(name), unquote(length(List.wrap(args))), unquote(quoted),
                     Module.delete_attribute(__MODULE__, :phi),
                     Module.delete_attribute(__MODULE__, :al)}
    end
  end

  defmacro __before_compile__(env) do
    entries = env.module |> Module.get_attribute(:lang_clauses) |> Enum.reverse()

    for {name, clauses} <- Enum.group_by(entries, &elem(&1, 0)) do
      quote do
        def unquote(name)() do
          %Rel{
            name: unquote(name),
            arity: unquote(clauses |> hd() |> elem(1)),
            clauses: unquote(Enum.map(clauses, &elem(&1, 2))),
            phi: unquote(Macro.escape(Enum.find_value(clauses, &elem(&1, 3)))),
            al: unquote(Macro.escape(Enum.find_value(clauses, &elem(&1, 4))))
          }
        end
      end
    end
  end

  @doc "I construct the relation named by the block's clauses."
  @spec rel(keyword()) :: Macro.t()
  defmacro rel(do: block) do
    clauses = Enum.map(lines(block), &collection/1)
    [{name, args, _body} | _] = clauses
    clauses = Enum.map(clauses, fn {^name, head, body} -> clause(name, head, body) end)

    quote do
      %Rel{name: unquote(name), arity: unquote(length(args)), clauses: unquote(clauses)}
    end
  end

  defp collection({name, _, args}) do
    args = List.wrap(args)

    case Enum.split(args, -1) do
      {head, [[do: body]]} -> {name, head, body}
      _fact -> {name, args, {:__block__, [], []}}
    end
  end

  defp clause(name, head, body) do
    {{head, body}, _} =
      Macro.prewalk({head, body}, 0, fn
        {:_, meta, ctx}, n -> {{:"_gensym#{n}", meta, ctx}, n + 1}
        node, n -> {node, n}
      end)

    head = Enum.map(head, &term(&1, {name, %{}}))
    scope = {name, Map.new(Term.names(head), &{&1, true})}
    clause = {head, Enum.with_index(lines(body), &goal(&1, &2, scope))}
    Macro.escape(clause, unquote: true)
  end

  defp lines({:__block__, _, forms}), do: forms
  defp lines(form), do: [form]

  defp term({:^, _, [expr]}, _scope), do: {:unquote, [], [expr]}
  defp term({:len, _, ctx}, _scope) when is_atom(ctx), do: :len
  defp term({:reify, _, [inner]}, scope), do: {:reify, goal(inner, 0, scope)}
  defp term(q, _scope) when is_integer(q), do: q
  defp term(s, scope) when is_binary(s), do: term(String.to_charlist(s), scope)
  defp term({:<<>>, _meta, parts}) do
    {prefix, tail} =
      case List.pop_at(parts, -1) do
        {{:"::", _, [tail, {:array, _, _}]}, prefix} -> {prefix, term(tail)}
        _closed -> {parts, nil}
      end

    Enum.reduce(Enum.reverse(prefix), tail, &{:cons, term(&1), &2})
  end

  defp term([], _scope), do: nil
  defp term([{:|, _, [h, t]}], scope), do: {:cons, term(h, scope), term(t, scope)}
  defp term([h | t], scope), do: {:cons, term(h, scope), term(t, scope)}
  defp term({name, _, ctx}, _scope) when is_atom(name) and is_atom(ctx), do: {:var, name}

  defp term({op, _, [a, b]}, scope) when op in [:+, :*],
    do: polynomial(if(op == :+, do: :add, else: :mul), term(a, scope), term(b, scope))

  defp term({:**, _, [a, q]}, scope) when is_integer(q) and q > 0,
    do: Enum.reduce(2..q//1, term(a, scope), fn _, acc -> {:mul, acc, term(a, scope)} end)

  defp term({:**, _, [_a, exponent]}, _scope),
    do:
      raise(ArgumentError, "an exponent is a positive integer, not #{Macro.to_string(exponent)}")

  defp term({:-, _, [q]}, _scope) when is_integer(q), do: -q
  defp term({:-, _, [a]}, scope), do: {:mul, term(a, scope), -1}
  defp term({:-, _, [a, b]}, scope) when is_integer(b), do: {:add, term(a, scope), -b}
  defp term({:-, _, [a, b]}, scope), do: {:add, term(a, scope), {:mul, term(b, scope), -1}}

  defp term({_callee, _, args} = call, scope) when is_list(args),
    do: {:papply, reference(call, scope), Enum.map(args, &term(&1, scope))}

  defp polynomial(tag, q, t) when is_integer(q) and not is_integer(t), do: {tag, t, q}
  defp polynomial(tag, t, u), do: {tag, t, u}

  defp goal({:=, _, [r, {:mod, _, [e, m]}]}, k, scope),
    do: {:call, primitive(:mod), [term(e, scope), term(m, scope), term(r, scope), hole(:q, k)]}

  defp goal({:=, _, [a, b]}, _k, scope), do: {:eq, term(a, scope), term(b, scope)}

  defp goal({op, _, [a, b]}, k, scope) when op in [:<, :>, :<=, :>=, :!=] do
    name = %{:< => :lt, :> => :gt, :<= => :lte, :>= => :gte, :!= => :neq}[op]
    {:call, primitive(name), [term(a, scope), term(b, scope), hole(:s, k)]}
  end

  defp goal({{:., _, [callback]}, _, args}, _k, scope),
    do: {:call, term(callback, scope), Enum.map(args, &term(&1, scope))}

  defp goal({callee, _, args}, _k, {_name, params} = scope)
       when is_map_key(params, callee) and is_list(args),
       do: {:call, {:var, callee}, Enum.map(args, &term(&1, scope))}

  defp goal({_callee, _, args} = call, _k, scope) when is_list(args),
    do: {:call, reference(call, scope), Enum.map(args, &term(&1, scope))}

  defp goal(form, _k, _scope),
    do: raise(ArgumentError, "a goal is an equation or a call, not #{Macro.to_string(form)}")

  defp hole(tag, k), do: {:var, :"_#{tag}#{k}"}
  defp primitive(name), do: reference({{:., [], [Zkfol.Prims, name]}, [], []}, {nil, %{}})
  defp reference({self, _, _args}, {self, _params}), do: self

  defp reference({callee, meta, _args}, _scope) do
    target = {callee, Keyword.put(meta, :no_parens, true), if(is_atom(callee), do: nil, else: [])}
    {:unquote, [], [{:&, [], [{:/, [], [target, 0]}]}]}
  end
end
