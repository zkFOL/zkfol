defmodule Examples.EAl do
  @moduledoc "I am the statement running as clauses: the derivation is the witness."

  use ExExample
  use Zkfol.Lang

  import ExUnit.Assertions

  alias Examples.EDoubling
  alias Examples.EUser
  alias Zkfol.Al
  alias Zkfol.Interpretation
  alias Zkfol.Pipeline
  alias Zkfol.Prover
  alias Zkfol.Refusal
  alias Zkfol.Statement
  alias Zkfol.Uair

  defrel pick(x, v) do
    tab(3, w)
    v = w + 1
  end

  defrel tab(1, 10)
  defrel tab(2, 20)
  defrel tab(3, 40)
  defrel tab(4, 40)

  defrel odd(1, 1)

  defrel odd(x, v) do
    x > 1
    even(x - 1, v)
  end

  defrel even(1, 0)

  defrel even(x, v) do
    x > 1
    odd(x - 1, v)
  end

  defrel pairs(1, 3, 5)
  defrel pairs(2, 4, 4)

  defrel twinned(x, v) do
    pairs(x, v, v)
  end

  defrel mate(x, v) do
    pairs(x, 3, v)
  end

  defrel loose(x) do
    pairs(x, _, _)
  end

  defrel both(1, 3)
  defrel both(1, 5)

  defrel summed(x, s) do
    both(x, a)
    both(x, b)
    a < b
    s = a + b
  end

  defrel capped(x, v) do
    x < 4
    v = x + 1
  end

  defrel forked(1, 0)

  defrel forked(x, v) do
    x > 1
    forked(x - 1, w)
    v = w + 1
    v < 100
  end

  defrel forked(x, v) do
    x > 1
    forked(x - 1, w)
    v = w + 10
    v < 1000
  end

  defrel regsm(1, 1, 1)

  defrel regsm(x, a, c) do
    x > 1
    regsm(x - 1, b, a)
    c = mod(a + b, 7919)
  end

  defrel shifty(m, x, v) do
    v = mod(x, m)
  end

  defrel collatz_next(x, y) do
    x = 2 * k
    y = k
  end

  defrel collatz_next(x, y) do
    x = 2 * k + 1
    y = 3 * x + 1
  end

  @doc "I give two names to the same value, without restricting it to a number."
  @spec variable_alias() :: Zkfol.Lang.Rel.t()
  example variable_alias do
    rel :variable_alias do
      variable_alias(x, y) do
        y = x
      end
    end
  end

  @doc "I resolve the alias in either direction for scalars, empty lists and nested lists."
  @spec aliased_values() :: Zkfol.Derivation.t()
  example aliased_values do
    relation = variable_alias()

    derivations =
      for value <- [7, [], [1, [2, 3]]], args <- [[value, :_], [:_, value]] do
        {:ok, derivation} = Al.derived(relation, args)

        assert Zkfol.Derivation.root(derivation, relation.name) ==
                 {relation.name, [value, value]}

        derivation
      end

    assert {:error, {:no_answer, _}} = Al.derived(relation, [[1], [2]])
    List.last(derivations)
  end

  @doc "I bind nothing, spelled two ways, so the first count answers."
  @spec no_arguments_lands_on_the_first_count() :: Interpretation.t()
  example no_arguments_lands_on_the_first_count do
    witness = Statement.witness(solved(EUser.fib(), []))

    assert Statement.witness(solved(EUser.fib(), [:_, :_])) == witness
    assert Interpretation.len(witness) == 1
    witness
  end

  @doc "Unguided doubling squares its cells past any machine, and the heap bound names it."
  @spec runaway_growth_is_refused() :: Refusal.t()
  example runaway_growth_is_refused do
    kernel = EDoubling.rewritten_fibonacci().rels |> hd()
    source = %Statement{rels: [kernel], args: [40]}
    {:error, Zkfol.Witness, reason, []} = Pipeline.run(EUser.plain(), source, heap: 200_000)

    assert {:heap_exhausted, _} = reason
    reason
  end

  @doc "A value aims the pointer: the call reads the column another row names."
  @spec hop_rel() :: Zkfol.Lang.Rel.t()
  example hop_rel do
    rel :hop do
      hop(1, 1)

      hop(x, v) do
        x > 0
        hop(v - 1, w)
        v = w + 1
      end
    end
  end

  @doc "Section 4 on the wire: the deref emits bits, a result row per read, and the Word lookup."
  @spec composed_hop_emits() :: Uair.t()
  example composed_hop_emits do
    {:ok, statement, _trace} =
      Zkfol.Pipeline.run(Zkfol.Pipeline.default(), %Statement{rels: [hop_rel()], args: [5]})

    witness = Statement.witness(statement)
    {:ok, uair} = Uair.emit(Statement.pred(statement), witness)
    len = Interpretation.len(witness)

    pointers = uair.mode.reads |> Enum.map(& &1.row) |> Enum.uniq()
    assert length(pointers) == 1

    for pointer <- pointers do
      slack = Enum.map(Enum.at(uair.columns, pointer), &(&1 - 1))

      assert Enum.any?(uair.limbs, fn {row, _limbs} ->
               Enum.at(uair.columns, row) == slack
             end)

      read = Enum.filter(uair.mode.reads, &(&1.row == pointer))

      assert [%{bit_rows: bits} | _rest] = read
      assert Enum.all?(read, &(&1.bit_rows == bits))

      bit_columns = for b <- bits, do: Enum.at(uair.columns, b)
      assert bit_columns |> List.flatten() |> Enum.all?(&(&1 in [0, 1]))

      weighted =
        Enum.zip_with(bit_columns, fn cells ->
          cells |> Enum.with_index() |> Enum.map(fn {b, i} -> b * 2 ** i end) |> Enum.sum()
        end)

      assert weighted == Enum.map(Enum.at(uair.columns, pointer), &(len - &1))
    end

    assert {:ok, %Prover.Report{}, _id} = Prover.prove_uair(uair, name: :composed_hop)
    uair
  end

  @doc "I am the pointer forged into the padding: only the region product refuses it."
  @spec an_out_of_region_read_is_refused() :: Refusal.t()
  example an_out_of_region_read_is_refused do
    uair = composed_hop_emits()
    [%{row: pointer, bit_rows: bits} | _rest] = uair.mode.reads
    len = uair.len

    spelled =
      for {b, nu} <- Enum.with_index(bits), do: {b, len |> Bitwise.bsr(nu) |> Bitwise.band(1)}

    read =
      for %{value_row: v, result_row: r} <- uair.mode.reads,
          do: {r, uair.columns |> Enum.at(v) |> Enum.at(len)}

    columns =
      Enum.reduce([{pointer, 0} | spelled] ++ read, uair.columns, fn {i, value}, cols ->
        List.update_at(cols, i, &List.replace_at(&1, 0, value))
      end)

    {:error, reason} = Prover.prove_uair(%{uair | columns: columns}, name: :forged_hop)
    assert {:verifier_rejected, _detail} = reason
    reason
  end

  @doc "A claimed row a read dereferences hands its claim to a bonded copy and stays private."
  @spec a_claimed_read_row_rides_a_copy() :: Prover.Report.t()
  example a_claimed_read_row_rides_a_copy do
    statement = solved(hop_rel(), [5])
    witness = Statement.witness(statement)
    {:ok, uair} = Uair.emit(Statement.pred(statement), witness, [{"out", 1, 2}])

    assert uair.num_public == 1
    assert [copy | _rest] = uair.rows
    assert copy > Interpretation.arity(witness)

    assert Enum.at(uair.columns, 0) ==
             Enum.at(uair.columns, Enum.find_index(uair.rows, &(&1 == 1)))

    assert uair.claims == [{"out", Interpretation.at(witness, 1, 2)}]
    assert Enum.all?(uair.mode.reads, &(&1.value_row >= uair.num_public))

    {:ok, report, _id} = Prover.prove_uair(uair, name: :claimed_read)
    report
  end

  @doc "I take a modulus the clause does not know: m times the quotient is a product of rows."
  @spec a_variable_modulus_reduces() :: Interpretation.t()
  example a_variable_modulus_reduces do
    assert Enum.to_list(Zkfol.stream(shifty(), [7, 30, :_])) == [[7, 30, 2]]
    Statement.witness(solved(shifty(), [7, 30, :_]))
  end

  @doc "Nothing steps tab, so its fact stands where pick reads it; the unreached never appear."
  @spec a_call_between_relations_derives() :: Interpretation.t()
  example a_call_between_relations_derives do
    assert Enum.to_list(Zkfol.stream([pick(), tab()], [1, :_])) == [[1, 41]]
    witness = Statement.witness(solved([pick(), tab()], [:_, 41]))

    assert Interpretation.len(witness) == 1
    assert Interpretation.at(witness, 1, 1) == 41
    witness
  end

  @doc "One name twice joins, an underscore keeps to itself, a literal pins its row."
  @spec outputs_unify_by_name_alone() :: Interpretation.t()
  example outputs_unify_by_name_alone do
    assert Enum.to_list(Zkfol.stream([twinned(), pairs()], [:_, :_])) == [[2, 4]]
    witness = Statement.witness(solved([twinned(), pairs()], [2, :_]))
    assert Interpretation.at(witness, 2, 1) == 4

    assert Enum.sort(Enum.to_list(Zkfol.stream([loose(), pairs()], [:_]))) == [[1], [2]]
    assert Enum.to_list(Zkfol.stream([mate(), pairs()], [:_, :_])) == [[1, 5]]
    witness
  end

  @doc "Evaluation never lowers: only the prove road wants a fresh body name on a row."
  @spec a_fresh_name_derives() :: Refusal.t()
  example a_fresh_name_derives do
    assert Enum.to_list(Zkfol.stream(collatz_next(), [7, :_])) == [[7, 22]]
    assert Enum.to_list(Zkfol.stream(collatz_next(), [8, :_])) == [[8, 4]]

    {:ok, derivation} = Al.derived(collatz_next(), [7], [])
    {:error, reason} = Zkfol.Phi.relaid(Zkfol.Statement.of(collatz_next()), derivation)

    assert {:unbound_variable, %{goals: [{:eq, {:var, :x}, {:add, {:mul, {:var, :k}, 2}, 1}}]}} =
             reason

    assert Refusal.message(reason) =~ "no clause binds"
    reason
  end

  @spec solved(Zkfol.Lang.Rel.t() | [Zkfol.Lang.Rel.t()], [Statement.datum() | :_]) ::
          Statement.t()
  defp solved(rels, args) do
    {:ok, statement, _trace} = Pipeline.run(EUser.plain(), Statement.of(rels, args: args))
    statement
  end
end
