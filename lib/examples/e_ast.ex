defmodule Examples.EAst do
  @moduledoc "I am the algebra's evidence: Figure 2's polynomial agrees with the oracle."

  use ExExample

  import ExUnit.Assertions

  alias Examples.EUser
  alias Zkfol.Ast
  alias Zkfol.Interpretation
  alias Zkfol.Statement
  alias Zkfol.Semantics

  @doc "A node list follows source order without discarding repeated leaves."
  @spec nodes_in_source_order() :: [Ast.pred() | Ast.term_t()]
  example nodes_in_source_order do
    cell = Ast.cell(1)
    sum = Ast.add(cell, 2)
    pred = Ast.eq(sum, cell)
    nodes = Ast.to_list(pred)
    assert nodes == [pred, sum, cell, 2, cell]
    assert Ast.to_list(7) == [7]
    nodes
  end

  @doc "Both directions: the polynomial vanishes exactly where the predicate holds."
  @spec figure_two_agrees_with_the_oracle() :: Zkfol.Ast.ep()
  example figure_two_agrees_with_the_oracle do
    phi = Statement.pred(EUser.power())
    poly = Ast.arithmetize(phi)
    witness = Statement.witness(EUser.power())
    tampered = tamper(witness, 3, 4, 9)
    columns = 1..Interpretation.len(witness)

    for x <- columns do
      assert Semantics.eval(poly, witness, x) == Semantics.eval(phi, witness, x)

      assert Semantics.eval(poly, tampered, x) == 0 == (Semantics.eval(phi, tampered, x) == 0),
             "column #{x} disagrees"
    end

    assert Enum.any?(columns, &(Semantics.eval(phi, tampered, &1) != 0))
    poly
  end

  @doc "A disjunction's degree is its branches' sum, a conjunction's their max."
  @spec the_degree_is_what_the_branches_multiply_to() :: non_neg_integer()
  example the_degree_is_what_the_branches_multiply_to do
    phi = Statement.pred(EUser.fibonacci())
    conjuncts = Ast.conjuncts(phi)

    assert Ast.degree(Ast.eq(Ast.cell(1), 1)) == 2
    assert Ast.degree(Ast.natural(Ast.cell(1))) == 0

    for conjunct <- conjuncts do
      assert Ast.degree(conjunct) == Enum.sum(Enum.map(Ast.branches(conjunct), &Ast.degree/1))
    end

    assert Ast.degree(phi) == Enum.max(Enum.map(conjuncts, &Ast.degree/1))
    assert Ast.degree(phi) < Zkfol.ZincPlus.pcs_params().degree
    Ast.degree(phi)
  end

  @doc "I am `witness` with the cell at row `i`, column `x`, made `value`."
  @spec tamper(Interpretation.t(), pos_integer(), pos_integer(), integer()) ::
          Interpretation.t()
  def tamper(witness, i, x, value), do: Interpretation.put(witness, i, x, value)
end
