defmodule Zkfol.Program do
  @moduledoc """
  I collect referenced definitions for the backends and identify their recursive members.

  ### Public API

  - `reached/2`: collect a root's dependencies without changing their clauses.
  - `recursive/1`: identify the members of call cycles in a collected program.
  """

  alias Zkfol.Lang.{Rel, Term}
  alias Zkfol.Refusal

  @doc "I collect each definition once; supplied definitions override constructors by name."
  @spec reached(Rel.t(), [Rel.t()]) :: {:ok, [Rel.t()]} | {:error, Refusal.t()}
  def reached(root, rels) do
    {:ok, collect([root], Map.new(rels, &{&1.name, &1}), %{})}
  catch
    {:refused, reason} -> {:error, reason}
  end

  defp collect([], _known, _seen), do: []

  defp collect([%Rel{name: name} | queue], known, seen) when is_map_key(seen, name),
    do: collect(queue, known, seen)

  defp collect([rel | queue], known, seen) do
    known = Map.put(known, rel.name, rel)
    dependencies = Enum.map(references(rel), &definition(&1, known))
    [rel | collect(queue ++ dependencies, known, Map.put(seen, rel.name, true))]
  end

  defp definition(ref, known) when is_function(ref, 0) do
    rel = ref.()
    Map.get(known, rel.name, rel)
  end

  defp definition(name, known),
    do: known[name] || throw({:refused, {:relation_not_in_scope, %{relation: name}}})

  @doc "I return relations on a call cycle, including cycles through passed relations."
  @spec recursive([Rel.t()]) :: MapSet.t(atom())
  def recursive(rels) do
    graph = :digraph.new()

    try do
      for rel <- rels, do: :digraph.add_vertex(graph, rel.name)

      for rel <- rels,
          ref <- references(rel),
          callee = Rel.name(ref),
          :digraph.vertex(graph, callee) != false,
          do: :digraph.add_edge(graph, rel.name, callee)

      graph |> :digraph_utils.cyclic_strong_components() |> List.flatten() |> MapSet.new()
    after
      :digraph.delete(graph)
    end
  end

  defp references(%Rel{clauses: clauses}) do
    clauses
    |> Enum.flat_map(fn {head, body} -> head ++ body end)
    |> Term.reduce([], fn
      {tag, ref, _args}, refs when tag in [:call, :papply] and not is_tuple(ref) -> [ref | refs]
      _node, refs -> refs
    end)
    |> Enum.reverse()
    |> Enum.uniq()
  end
end
