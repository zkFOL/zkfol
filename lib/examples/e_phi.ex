defmodule Examples.EPhi do
  @moduledoc "I am the lowering's evidence: inlined calls keep their locals, aliases and goal order."

  use ExExample
  use Zkfol

  import ExUnit.Assertions

  alias Examples.EAl
  alias Examples.EAlloc
  alias Examples.EUser
  alias Zkfol.Al
  alias Zkfol.Alloc
  alias Zkfol.Derivation
  alias Zkfol.Interpretation
  alias Zkfol.Lang.Rel
  alias Zkfol.Lay
  alias Zkfol.Phi
  alias Zkfol.Pipeline
  alias Zkfol.Semantics
  alias Zkfol.Statement
  alias Zkfol.Witness

  defrel local_factor(x) do
    natural(q)
    x = 3 * q
  end

  defrel local_calls(x, y) do
    each([x, y], local_factor())
  end

  defrel repeated_calls(x, y) do
    local_factor(x)
    local_factor(x)
    local_factor(y)
  end

  @doc "A clause-local q is filled from the derivation's bindings."
  @spec factored(pos_integer()) :: Statement.t()
  example factored(x \\ 6) do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [local_factor()], args: [x]})

    assert {{:local_factor, [x]}, %{x: x, q: div(x, 3)}} in Statement.derivation(statement).bindings
    assert Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  @spec factored_pair() :: Statement.t()
  example factored_pair do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [local_calls(), local_factor()], args: [6, 9]})

    assert [%Alloc.Member{relation: :local_calls}] = Statement.alloc(statement).members
    assert Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  @doc "A repeated goal is one obligation; each local keeps the call it came from."
  @spec repeated_factors() :: Statement.t()
  example repeated_factors do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{
        rels: [repeated_calls(), local_factor()],
        args: [6, 9]
      })

    [%{bindings: bindings}] = Statement.lay(statement).stands

    assert for(
             {slot, _value} <- bindings,
             slot.source.binding == {:variable, :q},
             do: slot.source.calls
           ) ==
             [[local_factor: 0], [local_factor: 2]]

    statement
  end

  defrel wrapped_calls(n, direct, first, second) do
    EAlloc.held(n, direct)
    EAlloc.delegated(n + 1, first)
    EAlloc.delegated(n + 1, second)
  end

  @spec recursive_relations() :: MapSet.t(atom())
  example recursive_relations do
    {:ok, relations} =
      Zkfol.Program.reached(wrapped_calls(), [wrapped_calls(), EAlloc.delegated(), EAlloc.held()])

    recursive = Zkfol.Program.recursive(relations)
    assert recursive == MapSet.new([:held])
    recursive
  end

  @doc "The wrapper leaves no member; both of its calls lay from the one fact they consume."
  @spec wrapped() :: Statement.t()
  example wrapped do
    rels = [wrapped_calls(), EAlloc.delegated(), EAlloc.held()]

    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: rels, args: [3, 6, 10, 10]})

    refute Enum.any?(Statement.alloc(statement).members, &(&1.relation == :delegated))
    assert Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  defrel division_calls(0, m, x, first, second) do
    first = mod(x, m)
    second = mod(x + 1, m)
  end

  defrel division_calls(1, m, x, first, second) do
    first = mod(x + 2, m)
    second = mod(x + 3, m)
  end

  @doc "The quotients stay local to the calls, and mod needs no member to fill them."
  @spec divided() :: Statement.t()
  example divided do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [division_calls()], args: [1, 5, 17, 4, 0]})

    assert [%Alloc.Member{relation: :division_calls}] = Statement.alloc(statement).members
    assert Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  defrel selected_list(0, xs, ys) do
    ys = xs
  end

  defrel selected_list(1, [_head | tail], ys) do
    ys = tail
  end

  defrel selected_head(selector, xs, head) do
    selected_list(selector, xs, ys)
    nth(1, ys, head)
  end

  @doc "Selecting the tail reads its head, not the head of the list handed in."
  @spec selected_second() :: Statement.t()
  example selected_second do
    rels = [selected_head(), selected_list()]

    assert Phi.compile(selected_head(), rels, [0, [10, 20, 30], 10]) ==
             Phi.compile(selected_head(), rels, [1, [10, 20, 30], 20])

    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: rels, args: [1, [10, 20, 30], 20]})

    assert Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  @spec aliased() :: Statement.t()
  example aliased do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [EAl.variable_alias()], args: [7, :_]})

    assert Derivation.root(Statement.derivation(statement), :variable_alias) ==
             {:variable_alias, [7, 7]}

    assert Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  defrel record_pair([_first, _second])

  defrel selected_record(1, [row], first, second) do
    first = second
    second = row
  end

  defrel selected_record(n, [row, next | tail], first, second) do
    n > 1
    selected_record(n - 1, [next | tail], _first, _second)
    first = second
    second = next
    record_pair(row)
    record_pair(next)
  end

  @doc "An output aliased before its record's width is known still opens the record's values."
  @spec selected_records() :: Lay.t()
  example selected_records do
    rels = [selected_record(), record_pair()]
    records = [[10, 11], [20, 21]]
    {:ok, pred, alloc} = Phi.compile(selected_record(), rels, [2, :_, :_, :_])
    {:ok, derivation} = Al.derived(rels, [2, records, :_, :_])
    lay = Lay.of(derivation, alloc)
    witness = Lay.witness(lay)
    assert Semantics.valid?(Alloc.link(pred, alloc), witness)

    for parameter <- [3, 4] do
      {:ok, claims} = Lay.claims(lay, [parameter])

      assert for(
               {name, row, column} <- claims,
               String.ends_with?(name, ".value"),
               do: Interpretation.at(witness, row, column)
             ) == List.last(records)
    end

    lay
  end

  @doc "I write output = middle * 2 before the equation that establishes middle."
  @spec equations() :: Rel.t()
  example equations do
    %Rel{
      name: :afterward,
      arity: 2,
      clauses: [
        {[{:var, :input}, {:var, :output}],
         [
           {:eq, {:var, :output}, {:mul, {:var, :middle}, 2}},
           {:eq, {:var, :middle}, {:add, {:var, :input}, 1}}
         ]}
      ]
    }
  end

  @doc "I derive and lay the same answer in either goal order, on the same predicate and allocation."
  @spec scheduled_equations() :: Statement.t()
  example scheduled_equations do
    relation = equations()
    [{head, goals}] = relation.clauses
    reversed = %{relation | clauses: [{head, Enum.reverse(goals)}]}
    assert {:ok, predicate, allocation} = Phi.compile(relation)
    assert Phi.compile(reversed) == {:ok, predicate, allocation}
    pipeline = %Pipeline{passes: [{Witness, []}, {Phi, []}]}

    statements =
      for relation <- [relation, reversed] do
        {:ok, statement, _trace} = Pipeline.run(pipeline, Statement.of(relation, args: [3, :_]))

        assert Zkfol.Derivation.root(Statement.derivation(statement), :afterward) ==
                 {:afterward, [3, 8]}

        assert Zkfol.Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
        statement
      end

    hd(statements)
  end

  defrel ordered_values(x, y) do
    y = x + 1
    x = 1
  end

  defrel constructed_list([h | t]) do
    ordered_values(h, last)
    append([last], [], t)
  end

  defrel counted_construction(n) do
    constructed_list(xs)
    length(xs, n)
  end

  @doc "The list built across two calls is counted without storing it or its calls."
  @spec construction() :: Statement.t()
  example construction do
    rels = [counted_construction(), constructed_list(), ordered_values()]
    {:ok, statement, _trace} = Pipeline.run(EUser.plain(), %Statement{rels: rels, args: [:_]})

    assert Derivation.root(Statement.derivation(statement), :counted_construction) ==
             {:counted_construction, [2]}

    assert Alloc.regions(Statement.alloc(statement)) == [counted_construction: 1, in: 1]
    statement
  end

  defrel alternatives(x, x)

  defrel alternatives(x, y) do
    natural(offset)
    y = x + offset
    1 = 2
  end

  defrel selected(x, y) do
    alternatives(x, y)
  end

  @doc "The contradicted alternative is discarded, and its local cell with it."
  @spec selected_alternative() :: Statement.t()
  example selected_alternative do
    {:ok, statement, _trace} =
      Pipeline.run(EUser.plain(), %Statement{rels: [selected(), alternatives()], args: [3, :_]})

    assert Derivation.root(Statement.derivation(statement), :selected) == {:selected, [3, 3]}
    assert Alloc.regions(Statement.alloc(statement)) == [selected: 2, in: 1]
    statement
  end
end
