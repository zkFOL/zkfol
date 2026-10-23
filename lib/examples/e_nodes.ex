defmodule Examples.ENodes do
  @moduledoc "I exercise constructed terms across calls, their sharing, and their proof obligations."
  use ExExample
  use Zkfol
  import ExUnit.Assertions

  alias Examples.EAst

  alias Zkfol.{
    Alloc,
    Derivation,
    Interpretation,
    Lay,
    Pipeline,
    Prover,
    Semantics,
    Statement,
    Uair
  }

  defrel joined([], ys, ys)

  defrel joined([h | t], ys, [h | zs]) do
    joined(t, ys, zs)
  end

  defrel rev([], [])

  defrel rev([h | t], r) do
    rev(t, rt)
    joined(rt, [h], r)
  end

  defrel tree(0, 0)

  defrel tree([l, r], s) do
    tree(l, sl)
    tree(r, sr)
    s = sl + sr + 1
  end

  defrel red(0, 0)
  defrel red(1, 1)

  defrel red([[1, x], _y], v) do
    red(x, v)
  end

  defrel red([[[0, x], y], z], v) do
    red([[x, z], [y, z]], v)
  end

  defrel terms(0)
  defrel terms([_h | _t])

  defrel optional_tail(_term)

  defrel optional_tail([_head | tail]) do
    optional_tail(tail)
  end

  defrel bridge(xs, s) do
    array([2], xs)
    tree(xs, s)
  end

  defrel same(x, y) do
    identical(x, y)
  end

  defrel identical(x, x)

  @doc "A clause reading a list leaves the generic clause free to take a scalar, zero included."
  @spec scalar_tail() :: Statement.t()
  example scalar_tail do
    assert Zkfol.Phi.compile(optional_tail(), nil, [0]) ==
             Zkfol.Phi.compile(optional_tail(), nil, [2])

    statement = solved(optional_tail(), [0])

    assert {:ok, [_ | _]} = Lay.claims(Statement.lay(statement), [1])
    assert Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    statement
  end

  @doc "A bridge proves the original bank at every addressed column."
  @spec a_view_keeps_its_source_cells() :: Statement.t()
  example a_view_keeps_its_source_cells do
    statement = solved(bridge(), [[0, 0], :_])
    alloc = Statement.alloc(statement)
    witness = Statement.witness(statement)
    row = Alloc.row(alloc, {:"bridge xs", 1})
    assert Enum.count(alloc.members, &is_struct(&1, Alloc.Bank)) == 1

    for x <- [2, 3] do
      forged = EAst.tamper(witness, row, x, 1)
      refute Semantics.valid?(Statement.pred(statement), forged)
    end

    assert {:ok, %Prover.Report{}, _id} = Prover.prove(Statement.pred(statement), witness)
    statement
  end

  @doc "An undeclared rank-three value keeps every scalar in shared term storage."
  @spec a_cube_keeps_every_cell() :: Statement.t()
  example a_cube_keeps_every_cell do
    cube = [[[1, 2], [3, 4]], [[5, 6], [7, 8]]]
    wrong = [[[1, 2], [99, 100]], [[5, 6], [101, 102]]]
    statement = solved(same(), [cube, :_])
    fact = {:same, [cube, wrong]}
    derivation = %Derivation{facts: [fact], clauses: [{fact, 0}]}
    forged = derivation |> Lay.of(Statement.alloc(statement)) |> Lay.witness()
    refute Semantics.valid?(Statement.pred(statement), forged)

    assert {:ok, %Prover.Report{}, _id} =
             Prover.prove(Statement.pred(statement), Statement.witness(statement))

    statement
  end

  @doc "Reverse allocates its constructed tails across calls; the source list remains a bank."
  @spec reverse([non_neg_integer()]) :: Statement.t()
  example reverse(xs \\ [1, 2, 3]) do
    n = length(xs)

    relation =
      rel :reversed do
        reversed(xs, ys) do
          array([^n], xs)
          rev(xs, ys)
        end
      end

    statement = solved(relation, [xs, :_])

    assert Derivation.root(Statement.derivation(statement), :reversed) ==
             {:reversed, [xs, Enum.reverse(xs)]}

    statement
  end

  @doc "Constructed lists and recursive trees prove without flattening their nested terms."
  @spec constructed_terms_prove() :: [Statement.t()]
  example constructed_terms_prove do
    reversed = reverse()

    assert Statement.bank(reversed, :"reversed xs") |> List.first() |> Enum.take(4) == [
             0,
             3,
             2,
             1
           ]

    for statement <- [reversed, solved(tree(), [[[0, 0], 0], :_])] do
      assert {:ok, %Prover.Report{}, _id} =
               Prover.prove(Statement.pred(statement), Statement.witness(statement))

      statement
    end
  end

  @doc "S constructs [[x,z],[y,z]] for a recursive call; both applications prove."
  @spec sk_proves() :: [Statement.t()]
  example sk_proves do
    statements =
      for term <- [[[1, 0], 1], [[1, 1], 0], [[[0, 1], 1], 0]] do
        statement = solved(red(), [term, :_])

        assert {:ok, %Prover.Report{}, _id} =
                 Prover.prove(Statement.pred(statement), Statement.witness(statement))

        statement
      end

    [zero, one, _constructed] = statements
    assert Statement.pred(zero) == Statement.pred(one)
    assert Statement.alloc(zero) == Statement.alloc(one)
    statements
  end

  @doc "Equal subterms share an identity, and even unread children must be real earlier nodes."
  @spec children_are_shared_and_bounded() :: Statement.t()
  example children_are_shared_and_bounded do
    statement = solved(terms(), [[[1, 2], [1, 2]]])
    alloc = Statement.alloc(statement)
    witness = Statement.witness(statement)
    [%Alloc.Slot{allocation: {:node, root}}] = Alloc.root(alloc).slots
    id = Interpretation.at(witness, Alloc.row(alloc, root), 1)
    head = Alloc.row(alloc, {Zkfol.Nodes, :head})
    tail = Alloc.row(alloc, {Zkfol.Nodes, :tail})
    next = Interpretation.at(witness, tail, id)
    assert Interpretation.at(witness, head, id) == Interpretation.at(witness, head, next)

    for {row, value} <- [{head, 0}, {tail, 0}, {head, id}, {tail, id}] do
      forged = EAst.tamper(witness, row, id, value)

      refute Semantics.valid?(Statement.pred(statement), forged)
      assert {:error, _refusal} = Uair.emit(Statement.pred(statement), forged)
    end

    statement
  end

  @doc "Opening a term binds its reachable scalar values, not merely its identity."
  @spec opening_binds_structure() :: Uair.t()
  example opening_binds_structure do
    statement = children_are_shared_and_bounded()
    witness = Statement.witness(statement)
    {:ok, claims} = Lay.claims(Statement.lay(statement), [1])
    values = for {name, row, x} <- claims, String.ends_with?(name, ".value"), do: {row, x}
    assert length(values) == 2
    {:ok, uair} = Uair.emit(Statement.pred(statement), witness, claims)
    assert {:ok, %Prover.Report{}, _id} = Prover.prove_uair(uair)
    [{row, x} | _] = values
    # Alter a public scalar throughout its declared column; the saved opening must reject it.
    column = Enum.find_index(uair.rows, &(&1 == row))
    forged = List.update_at(uair.columns, column, &List.replace_at(&1, uair.len - x, 9))
    assert {:error, _refusal} = Prover.prove_uair(%{uair | columns: forged})
    uair
  end

  @spec solved(Zkfol.Lang.Rel.t(), [term()], keyword()) :: Statement.t()
  defp solved(rel, args, opts \\ []) do
    {:ok, statement, _trace} =
      Pipeline.run(Examples.EUser.plain(), %Statement{rels: [rel], args: args}, opts)

    assert Semantics.valid?(Statement.pred(statement), Statement.witness(statement))
    assert Examples.EFace.bridged(statement) == statement
    statement
  end
end
