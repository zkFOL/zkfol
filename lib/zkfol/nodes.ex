defmodule Zkfol.Nodes do
  @moduledoc """
  I am the shared term table and its expression-named rows. The predicate and witness
  derive those rows from the same graph; a constructor alone spends nothing.

  ### Public API

  - `lower/2`: realize demanded terms and bank bridges in the predicate and allocation.
  - `cells/4`: derive table and generated cells from the allocation’s producers.
  - `openings/4`: bind the fields of a reachable term graph.
  """
  use TypedStruct
  alias Zkfol.{Alloc, Ast, Interpretation}
  alias Zkfol.Phi.{Place, Value}

  require Place

  typedstruct enforce: true do
    field(:name, atom(), default: __MODULE__)
    field(:refs, [Ast.row_ref()])
  end

  @doc "I realize the reads a predicate demands, returning their allocation beside it."
  @spec lower(Ast.pred(), [Alloc.Member.t() | Alloc.Bank.t()]) ::
          {Ast.pred(), [Alloc.Member.t() | Alloc.Bank.t() | t()]}
  def lower(pred, members) do
    stored =
      for %Alloc.Member{slots: slots} <- members,
          %Alloc.Slot{allocation: {:node, ref}} <- slots,
          do: ref

    if stored != [] or Enum.any?(references(pred), &match?({__MODULE__, _}, &1)) do
      expanded = expand(pred, MapSet.new())

      bridges =
        for {__MODULE__, {:suffix, source}} <- references(expanded),
            do: expand(bridge(source), MapSet.new())

      unread = stored -- Ast.pointer_reads(expanded)

      bounds =
        for ref <- unread do
          Ast.conj([
            Ast.natural(Ast.add(Ast.cell(ref), -1)),
            Ast.natural(Ast.add(Ast.len(), Ast.mul(Ast.cell(ref), -1)))
          ])
        end

      pred = Ast.conj([expanded, schema() | bridges ++ bounds])
      refs = Enum.uniq(for {__MODULE__, _} = ref <- references(pred), do: ref)
      {pred, members ++ [%__MODULE__{refs: refs}]}
    else
      {pred, members}
    end
  end

  defp expand({:disj, choices}, seen),
    do: Ast.disj(Enum.map(choices, &expand(&1, seen)))

  defp expand(pred, seen) do
    {choices, atoms} = Enum.split_with(Ast.conjuncts(pred), &match?({:disj, _}, &1))
    keys = atoms |> Enum.flat_map(&needs/1) |> Enum.uniq() |> Enum.reject(&(&1 in seen))
    seen = Enum.into(keys, seen)
    definitions = Enum.map(keys, &expand(definition(&1), seen))
    branches = Enum.map(choices, &expand(&1, seen))
    Ast.conj(Enum.uniq(atoms ++ definitions ++ branches))
  end

  defp references(pred), do: Enum.uniq(Ast.reads(pred) ++ Ast.pointer_reads(pred))

  defp needs(pred) do
    Ast.reduce(pred, :ok, fn node, :ok ->
      case Ast.read(node) do
        {{__MODULE__, {op, _value}}, address}
        when op in [:read, :node] and address != {:at, :x, 1, 0} ->
          throw({:refused, {:unliftable_term, %{term: node}}})

        _read ->
          :ok
      end
    end)

    generated = for {__MODULE__, {op, _value}} = ref <- references(pred), op != :suffix, do: ref

    scalar =
      for {{__MODULE__, :value}, pointer} <- Ast.pointer_derefs(pred), do: {:scalar, pointer}

    Enum.uniq(generated ++ scalar)
  end

  defp definition({:scalar, pointer}),
    do: Ast.eq(Ast.cell({__MODULE__, :tag}, pointer), 1)

  defp definition({__MODULE__, {:read, expr}} = row), do: Ast.eq(Ast.cell(row), expr)

  defp definition({__MODULE__, {:node, value}} = row),
    do: node(Ast.cell(row), value)

  defp bridge(source = {bank, dimensions}) do
    row = {__MODULE__, {:suffix, source}}
    id = Ast.cell(row)
    view = %Place.View{bank: bank, head: Ast.address(:x, 1, 0), dimensions: dimensions}
    head = Place.slice(view, 0)

    Ast.disj([
      Ast.conj([Ast.eq(Ast.cell({:in, bank}), 0), Ast.eq(id, 1)]),
      Ast.conj([
        Ast.eq(Ast.cell({:in, bank}), 1),
        node(id, {:pair, head, {:node, Ast.at(row, :x, 1, -1)}})
      ])
    ])
  end

  # What the node with this id holds, as equations on its fields.
  @spec node(Ast.term_t(), term()) :: Ast.pred()
  defp node(id, {:node, other}), do: Ast.eq(id, other)
  defp node(id, []), do: Ast.eq(id, 1)
  defp node(id, [h | t]), do: node(id, {:pair, h, t})

  defp node(id, {:pair, h, t}) do
    Ast.conj([
      Ast.eq(Place.read(:tag, id), 2),
      Ast.eq(Place.read(:head, id), elem(Place.node_of(h), 1)),
      Ast.eq(Place.read(:tail, id), elem(Place.node_of(t), 1))
    ])
  end

  # A view is the term its bank suffix bridge realizes.
  defp node(id, %Place.View{bank: bank, head: head, dimensions: dimensions}) do
    {:at, base, m, a} = head
    Ast.eq(id, Ast.at({__MODULE__, {:suffix, {bank, dimensions}}}, base, m, a))
  end

  defp node(id, scalar) do
    Ast.conj([
      Ast.eq(Place.read(:tag, id), 1),
      Ast.eq(Place.read(:value, id), Value.scalar(scalar))
    ])
  end

  defp schema do
    tag = Ast.cell({__MODULE__, :tag})
    value = Ast.cell({__MODULE__, :value})
    head = Ast.cell({__MODULE__, :head})
    tail = Ast.cell({__MODULE__, :tail})
    cons = Ast.mul(tag, Ast.add(tag, -1))

    Ast.conj([
      Ast.disj([
        Ast.conj([Ast.eq(tag, 0), Ast.eq(value, 0), Ast.eq(head, 1), Ast.eq(tail, 1)]),
        Ast.conj([Ast.eq(tag, 1), Ast.eq(head, 1), Ast.eq(tail, 1)]),
        Ast.conj([Ast.eq(tag, 2), Ast.eq(value, 0)])
      ]),
      Ast.natural(Ast.add(head, -1)),
      Ast.natural(Ast.add(tail, -1)),
      Ast.natural(Ast.mul(cons, Ast.add(Ast.add(:x, Ast.mul(head, -1)), -1))),
      Ast.natural(Ast.mul(cons, Ast.add(Ast.add(:x, Ast.mul(tail, -1)), -1))),
      Ast.eq(Ast.at({__MODULE__, :tag}, :x, 0, 1), 0)
    ])
  end

  @doc "I lay table identities and evaluate generated rows from the ordinary cells."
  @spec cells(t(), Alloc.t(), map(), %{pos_integer() => 1}) :: map()
  def cells(%__MODULE__{refs: refs}, alloc, cells, defaults) do
    terms =
      Enum.uniq([
        []
        | Enum.flat_map(cells, fn
            {_at, {:node, term}} -> subterms(term)
            _cell -> []
          end)
      ])

    ids = Map.new(Enum.with_index(terms, 1))
    terms = Map.new(Enum.with_index(terms, 1), fn {term, id} -> {id, term} end)

    cells =
      Map.new(cells, fn
        {at, {:node, term}} -> {at, Map.fetch!(ids, term)}
        pair -> pair
      end)

    table =
      for {id, term} <- terms,
          {field, v} <- Enum.zip([:tag, :value, :head, :tail], encoded(term, ids)),
          do: {{Alloc.row(alloc, {__MODULE__, field}), id}, v}

    cells = Map.merge(cells, Map.new(table))
    len = Enum.max(for {{_r, x}, _v} <- cells, do: x)
    generated = for {__MODULE__, {_op, _value}} = ref <- refs, x <- 1..len, do: {ref, x}

    ctx = %{
      cells: cells,
      len: len,
      rows: Map.new(Enum.with_index(Alloc.refs(alloc), 1)),
      ids: ids,
      terms: terms,
      defaults: defaults
    }

    produced =
      for {ref, x} <- generated do
        value = read(ref, x, ctx)
        {{Alloc.row(alloc, ref), x}, if(value == :error, do: 1, else: value)}
      end

    Map.merge(cells, Map.new(produced))
  end

  @doc "I open a reachable term graph, sharing fields reached through several paths."
  @spec openings(Alloc.t(), Interpretation.t(), pos_integer(), String.t()) ::
          [{String.t(), Ast.row_ref(), pos_integer()}]
  def openings(alloc, witness, id, name), do: opened([{id, name}], MapSet.new(), alloc, witness)

  defp opened([], _seen, _alloc, _witness), do: []

  defp opened([{id, name} | rest], seen, alloc, witness) do
    if id in seen do
      opened(rest, seen, alloc, witness)
    else
      tag = Interpretation.at(witness, Alloc.row(alloc, {__MODULE__, :tag}), id)

      fields =
        case tag do
          0 -> [:tag]
          1 -> [:tag, :value]
          2 -> [:tag, :head, :tail]
        end

      named =
        for field <- fields, do: {name <> "." <> Atom.to_string(field), {__MODULE__, field}, id}

      children =
        for field <- fields,
            field in [:head, :tail],
            do:
              {Interpretation.at(witness, Alloc.row(alloc, {__MODULE__, field}), id),
               name <> "." <> Atom.to_string(field)}

      named ++ opened(rest ++ children, MapSet.put(seen, id), alloc, witness)
    end
  end

  defp subterms(q) when is_integer(q), do: [q]
  defp subterms([]), do: [[]]
  defp subterms([h | t] = list), do: subterms(h) ++ subterms(t) ++ [list]
  defp subterms(_free), do: [0]
  defp encoded([], _ids), do: [0, 0, 1, 1]
  defp encoded(q, _ids) when is_integer(q), do: [1, q, 1, 1]
  defp encoded([h | t], ids), do: [2, 0, Map.fetch!(ids, h), Map.fetch!(ids, t)]

  defp read(ref, x, ctx) do
    case Map.fetch(ctx.cells, {Map.fetch!(ctx.rows, ref), x}) do
      {:ok, value} -> value
      :error -> generated(ref, x, ctx)
    end
  end

  defp generated({__MODULE__, {:read, expr}}, x, ctx), do: eval(expr, x, ctx)

  defp generated({__MODULE__, {:node, value}}, x, ctx),
    do: Map.get(ctx.ids, ground(value, x, ctx), :error)

  defp generated(ref, _x, ctx), do: Map.get(ctx.defaults, Map.fetch!(ctx.rows, ref), 0)

  defp ground({:node, id}, x, ctx), do: Map.get(ctx.terms, eval(id, x, ctx), :error)
  defp ground({:pair, h, t}, x, ctx), do: [ground(h, x, ctx) | ground(t, x, ctx)]
  defp ground([h | t], x, ctx), do: [ground(h, x, ctx) | ground(t, x, ctx)]
  defp ground([], _x, _ctx), do: []

  # A list in a bank ends at column one, so its length is its head column minus one.
  defp ground(laid, x, ctx) when Place.is_laid(laid) do
    {:at, base, m, a} = laid.head
    len = eval(Ast.add(Ast.mul(base, m), a - 1), x, ctx)
    for i <- 0..(len - 1)//1, do: ground(Place.slice(laid, i), x, ctx)
  end

  defp ground(value, x, ctx), do: eval(Value.scalar(value), x, ctx)

  defp eval(expr, x, ctx), do: Zkfol.Semantics.eval(expr, ctx.len, x, &read(&1, &2, ctx))
end
