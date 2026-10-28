defmodule Zkfol.Phi.Expression do
  @moduledoc """
  I substitute a walk's bindings into a term, leaving unknown names as variables.

  Substitution replaces names without evaluating the term. A complete expression can
  be read as arithmetic or passed to a call; an incomplete sum can identify its unknown.
  Unallocated parameters keep their identity. Only arithmetic reads them as scalars.

  ### Public API

  - `scoped/2`: qualify source variables by call site.
  - `callee/4`: resolve a named or passed relation and its arguments.
  - `substitute/2`: the term with its known names substituted.
  - `resolve/2`, `resolve!/2`: the expression, or the names still needed.
  - `argument/2`: the value handed to a call, retaining a parameter's identity.
  - `dependencies/2`: unresolved names and parameter identities in a term.
  - `solve/2`: the expression, or its one unknown in a sum.
  """

  alias Zkfol.Ast
  alias Zkfol.Lang.Term
  alias Zkfol.Phi.{Place, Value, Walk}

  @typedoc "A source name, qualified by its call site when its clause is inlined."
  @type name :: atom() | {[atom() | non_neg_integer()], atom()}

  @type symbolic ::
          Ast.poly(
            Value.t()
            | {:var, name()}
            | nil
            | {:cons, symbolic(), symbolic()}
            | {:papply, Term.name(), [symbolic()]}
          )
          | [symbolic()]
  @type dependency ::
          name() | Ast.row_ref() | {:storage | :scalar, Ast.row_ref()} | {:array, name()}
  @type waiting :: {:waiting, [dependency()]}
  @type result :: {:ok, Value.t()} | waiting()

  @doc "I qualify source variables by their call site."
  @spec scoped(term(), [atom() | non_neg_integer()]) :: term()
  def scoped({:var, name}, scope), do: {:var, {scope, name}}

  def scoped({op, a, b}, scope) when op in [:eq, :add, :mul, :cons],
    do: {op, scoped(a, scope), scoped(b, scope)}

  def scoped({:call, q, args}, scope), do: {:call, scoped(q, scope), scoped(args, scope)}
  def scoped({:papply, q, args}, scope), do: {:papply, q, scoped(args, scope)}
  def scoped({:reify, goal}, scope), do: {:reify, scoped(goal, scope)}
  def scoped(terms, scope) when is_list(terms), do: Enum.map(terms, &scoped(&1, scope))
  def scoped(leaf, _scope), do: leaf

  @doc "I resolve a named or passed relation and prepend its captured arguments."
  @spec callee(term(), [term()], Walk.t(), %{atom() => Zkfol.Lang.Rel.t()}) ::
          {:ok, Zkfol.Lang.Rel.t(), [term()]} | waiting()
  def callee({:var, _} = q, args, walk, scope) do
    with {:ok, value} <- resolve(q, walk) do
      case value do
        {:rel, p, fixed} -> callee(p, fixed ++ args, walk, scope)
        {:fresh, ref} -> {:waiting, [ref]}
        other -> throw({:refused, {:unliftable_term, %{term: other}}})
      end
    end
  end

  def callee(q, args, _walk, scope) do
    name = Zkfol.Lang.Rel.name(q)
    {:ok, scope[name] || throw({:refused, {:relation_not_in_scope, %{relation: name}}}), args}
  end

  @doc "I substitute known bindings without assigning a value to an unknown name."
  @spec substitute(term(), Walk.t()) :: symbolic()
  def substitute(variable = {:var, name}, walk) do
    case Map.get(walk.env, name, :fresh) do
      :fresh -> variable
      value -> substitute(value, walk)
    end
  end

  def substitute(nil, _walk), do: nil

  def substitute(term, walk),
    do: map_children(term, &substitute(&1, walk), &Walk.follow(walk, &1))

  @doc "I read an expression, reporting the names still needed."
  @spec resolve(term(), Walk.t()) :: result()
  def resolve(term, walk) do
    value = substitute(term, walk)

    case Term.names(value) do
      [] -> {:ok, read(value)}
      missing -> {:waiting, Enum.uniq(missing)}
    end
  end

  @doc "I collect unresolved names and parameter identities after following aliases."
  @spec dependencies(term(), Walk.t()) :: [name() | Ast.row_ref()]
  def dependencies(term, walk), do: term |> substitute(walk) |> missing() |> Enum.uniq()

  defp missing({tag, name}) when tag in [:var, :fresh], do: [name]
  defp missing(term) when is_tuple(term), do: term |> Tuple.to_list() |> missing()
  defp missing(terms) when is_list(terms), do: Enum.flat_map(terms, &missing/1)
  defp missing(_literal), do: []

  @doc "I require an expression whose variables have values."
  @spec resolve!(term(), Walk.t()) :: Value.t()
  def resolve!(term, walk) do
    case resolve(term, walk) do
      {:ok, value} -> value
      {:waiting, [name | _]} -> throw({:refused, {:unbound_variable, %{variable: name}}})
    end
  end

  @doc "I pass a complete value or unresolved parameter; an unknown expression passes a wildcard."
  @spec argument(term(), Walk.t()) :: Value.t()
  def argument(term, walk) do
    value = substitute(term, walk)

    case Term.names(value) do
      [] -> read(value)
      _names -> :fresh
    end
  end

  @doc "I return a complete expression, or the one unknown and the rest of its sum."
  @spec solve(term(), Walk.t()) ::
          {:ok, Value.t()} | {:free, name(), Value.scalar()} | waiting()
  def solve(term, walk) do
    value = substitute(term, walk)
    {known, unknown} = Enum.split_with(summands(value, []), &(Term.names(&1) == []))

    case unknown do
      [] ->
        {:ok, read(value)}

      [{:var, name}] ->
        rest = known |> Enum.map(&Value.scalar(read(&1))) |> Enum.reduce(0, &Ast.add/2)
        {:free, name, rest}

      _several ->
        {:waiting, Enum.uniq(Term.names(unknown))}
    end
  end

  defp read(term) do
    case map_children(term, &read/1) do
      {:add, a, b} -> Ast.add(Value.scalar(a), Value.scalar(b))
      {:mul, a, b} -> Ast.mul(Value.scalar(a), Value.scalar(b))
      {:cons, h, t} -> Place.consed(h, t)
      {:papply, p, fixed} -> {:rel, Zkfol.Lang.Rel.name(p), fixed}
      nil -> []
      value -> value
    end
  end

  defp summands({:add, a, b}, rest), do: summands(a, summands(b, rest))
  defp summands(value, rest), do: [value | rest]

  defp map_children(term, fun, leaf \\ & &1)

  defp map_children({op, a, b}, fun, _leaf) when op in [:add, :mul, :cons],
    do: {op, fun.(a), fun.(b)}

  defp map_children({:papply, p, fixed}, fun, _leaf), do: {:papply, p, Enum.map(fixed, fun)}
  defp map_children(terms, fun, _leaf) when is_list(terms), do: Enum.map(terms, fun)
  defp map_children(value, _fun, leaf), do: leaf.(value)
end
