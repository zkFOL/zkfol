defmodule Zkfol.Phi.Expression do
  @moduledoc """
  I substitute a walk's bindings into a term, leaving unknown names as variables.

  Substitution replaces names without evaluating the term. A complete expression can
  be read as arithmetic or passed to a call; an incomplete sum can identify its unknown.

  ### Public API

  - `substitute/2`: the term with its known names substituted.
  - `resolve/2`, `resolve!/2`: the expression, or the names still needed.
  - `argument/2`: the value handed to a call, retaining a parameter's identity.
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
  @type waiting :: {:waiting, [name()]}
  @type result :: {:ok, Value.t()} | waiting()

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
      [] -> {:ok, read(value, walk)}
      missing -> {:waiting, Enum.uniq(missing)}
    end
  end

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

    case {term, value, Term.names(value)} do
      {{:var, _name}, fresh = {:fresh, _ref}, []} -> fresh
      {_term, value, []} -> read(value, walk)
      {_term, _value, _names} -> :fresh
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
        {:ok, read(value, walk)}

      [{:var, name}] ->
        rest = known |> Enum.map(&Value.scalar(read(&1, walk))) |> Enum.reduce(0, &Ast.add/2)
        {:free, name, rest}

      _several ->
        {:waiting, Enum.uniq(Term.names(unknown))}
    end
  end

  defp read(term, walk) do
    case map_children(term, &read(&1, walk)) do
      {:add, a, b} -> Ast.add(Value.scalar(a), Value.scalar(b))
      {:mul, a, b} -> Ast.mul(Value.scalar(a), Value.scalar(b))
      {:cons, h, t} -> Place.consed(h, t, walk.shapes)
      {:papply, p, fixed} -> {:rel, Zkfol.Lang.Rel.name(p), fixed}
      fresh = {:fresh, _ref} -> Value.scalar(fresh)
      nil -> []
      value -> Value.shaped(value, walk.shapes)
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
