defmodule Examples.EArrays do
  @moduledoc "I exercise declared arrays, shared traversal rows and structural matching."
  use ExExample
  use Zkfol
  import ExUnit.Assertions

  alias Zkfol.{Al, Alloc, Ast, Interpretation, Lay, Phi, Program, Prover, Semantics, Uair, Unfold}
  alias Zkfol.Lang.Rel
  alias Examples.{ENodes, EPhi, EUser}

  defrel doubled(<<>>, <<>>)

  defrel doubled(<<x, xs::array>>, <<y, ys::array>>) do
    y = 2 * x
    doubled(xs, ys)
  end

  defrel copied(<<>>, <<>>)

  defrel copied(<<x, xs::array>>, <<x, ys::array>>) do
    copied(xs, ys)
  end

  defrel checked_suffixes(<<>>)

  defrel checked_suffixes(<<h, t::array>>) do
    array([1], [0 | t])
    natural(h)
    checked_suffixes(t)
  end

  defrel distinct_suffixes(<<>>)

  defrel distinct_suffixes(<<h, t::array>>) do
    distinct_cells(<<h, t::array>>)
    distinct_suffixes(t)
  end

  defrel distinct_cells(xs) do
    all_distinct(xs)
  end

  defrel mapped(xs, ys) do
    map(xs, EUser.succ(), ys)
  end

  defrel declared(xs, ys) do
    array([3], xs)
    array([3], ys)
    doubled(xs, ys)
  end

  defrel wrapped(xs, ys) do
    declared(xs, ys)
  end

  defrel invoke(p, xs, ys) do
    p(xs, ys)
  end

  defrel passed(xs, ys) do
    invoke(declared(), xs, ys)
  end

  defrel nested(xs, ys) do
    map(xs, mapped(), ys)
  end

  defrel transposed_map(xs, ys) do
    column(xs, columns)
    map(columns, mapped(), results)
    column(results, ys)
  end

  defrel repeated(xs, ys, zs) do
    map(xs, EUser.succ(), ys)
    map(ys, EUser.succ(), zs)
  end

  defrel reversed_clauses(<<x, xs::array>>, <<y, ys::array>>) do
    reversed_clauses(xs, ys)
    y = x + 1
  end

  defrel reversed_clauses(<<>>, <<>>)

  defrel filtered(<<>>, <<>>)

  defrel filtered(<<x, xs::array>>, <<y, ys::array>>) do
    x > 0
    y = x + 1
    filtered(xs, ys)
  end

  defrel fixed_private(k, xs, ys) do
    map(xs, bump_by(k), ys)
  end

  defrel bump_by(k, x, y) do
    y = k + x
  end

  defrel sized(0, xs) do
    array([2], xs)
    xs = [7, 8]
  end

  defrel sized(1, xs) do
    array([3], xs)
    xs = [1, 2, 3]
  end

  defrel row_total(xs, total) do
    array([2], xs)
    xs = [a, b]
    total = a + b
  end

  defrel totals(xs, ys) do
    map(xs, row_total(), ys)
  end

  defrel checked_transpose(xs) do
    array([2, 3], xs)
    column(xs, columns)
    array([3, 2], columns)
    columns = [[1, 4], [2, 5], [3, 6]]
  end

  @doc "Different clauses establish different shapes in one compiled relation."
  @spec conditional_shapes() :: [Lay.t()]
  example conditional_shapes do
    {:ok, pred, alloc} = Phi.compile(sized())
    pred = Alloc.link(pred, alloc)

    for choice <- [0, 1] do
      {:ok, derivation} = Al.derived(sized(), [choice, :_])
      lay = Lay.of(derivation, alloc)
      assert Semantics.valid?(pred, Lay.witness(lay))
      {:ok, claims} = Lay.claims(lay, [1, 2])
      assert {:ok, %Prover.Report{}, _id} = Prover.prove(pred, Lay.witness(lay), claims: claims)
      lay
    end
  end

  @doc "An array inside a recursive call has independent cells on every invocation."
  @spec local_arrays() :: Lay.t()
  example local_arrays do
    {_pred, lay} = laid(totals(), [[[1, 2], [4, 5]], :_], %{})
    assert Zkfol.Derivation.root(lay.derivation, :totals) == {:totals, [[[1, 2], [4, 5]], [3, 9]]}
    lay
  end

  @doc "Checking a transposed view's shape reuses the source bank."
  @spec checked_view() :: Lay.t()
  example checked_view do
    {_pred, lay} = laid(checked_transpose(), [[[1, 2, 3], [4, 5, 6]]], %{})
    assert Enum.count(lay.alloc.members, &is_struct(&1, Alloc.Bank)) == 1

    refute Enum.any?(
             Alloc.root(lay.alloc).slots,
             &match?(%Alloc.Slot{allocation: {:record, _}}, &1)
           )

    lay
  end

  @doc "Array dimensions can arrive through aliases and several rounds of deferred equations."
  @spec deferred_dimensions() :: Lay.t()
  example deferred_dimensions do
    root =
      rel do
        deferred_grid(xs) do
          array([rows, cols], xs)
          rows = side + 0
          cols = depth
          side = last + 0
          depth = side + 0
          last = 2
          xs = [[1, 2], [3, 4]]
        end
      end

    {_pred, lay} = laid(root, [[[1, 2], [3, 4]]], %{})
    lay
  end

  @doc "Empty axes, nested maps, private captures and transposed views preserve source answers."
  @spec composed_traversals() :: [Lay.t()]
  example composed_traversals do
    cases = [
      {doubled(), [[], :_], %{0 => [0], 1 => [0]}, []},
      {doubled(), [[3], :_], %{0 => [1], 1 => [1]}, [:doubled]},
      {mapped(), [[1, 2, 3], :_], %{0 => [3], 1 => [3]}, [:map]},
      {nested(), [[[1, 2, 3], [4, 5, 6]], :_], %{0 => [2, 3], 1 => [2, 3]}, [:map]},
      {transposed_map(), [[[1, 2, 3], [4, 5, 6]], :_], %{0 => [2, 3], 1 => [2, 3]}, []},
      {repeated(), [[1, 2, 3], :_, :_], %{0 => [3], 1 => [3], 2 => [3]}, [:map, :map]},
      {reversed_clauses(), [[1, 2, 3], :_], %{0 => [3], 1 => [3]}, [:reversed_clauses]},
      {filtered(), [[1, 2, 3], :_], %{0 => [3], 1 => [3]}, [:filtered]},
      {fixed_private(), [4, [1, 2, 3], :_], %{1 => [3], 2 => [3]}, []},
      {copied(), [[[[1, 2], [3, 4]], [[5, 6], [7, 8]]], :_], %{0 => [2, 2, 2], 1 => [2, 2, 2]},
       [:copied]},
      {checked_suffixes(), [[7]], %{0 => [1]}, [:checked_suffixes]},
      {distinct_suffixes(), [[1, 2, 3]], %{0 => [3]}, [:distinct_suffixes]},
      {ENodes.same(), [[[], []], :_], %{0 => [2, 0], 1 => [2, 0]}, []}
    ]

    for {rel, args, arrays, loops} <- cases do
      {_pred, lay} = laid(rel, args, arrays)

      assert for(%Alloc.Member{steps: {_, _}, relation: name} <- lay.alloc.members, do: name) ==
               loops

      lay
    end
  end

  @doc "Higher ranks and empty axes use the same view and preserve every cell through a heap call."
  @spec higher_rank_views() :: [Lay.t()]
  example higher_rank_views do
    for {dimensions, input} <- [
          {[2, 2, 2], [[[1, 2], [3, 4]], [[5, 6], [7, 8]]]},
          {[2, 1, 1, 2], [[[[1, 2]]], [[[3, 4]]]]},
          {[0, 2, 3], []},
          {[2, 0, 3], [[], []]},
          {[2, 2, 0], [[[], []], [[], []]]}
        ] do
      {pred, lay} = laid(ENodes.rev(), [input, :_], %{0 => dimensions})
      witness = Lay.witness(lay)

      for bank = %Alloc.Bank{} <- lay.alloc.members,
          Enum.product(dimensions) > 0,
          row <- 1..bank.depth,
          column <- 2..(hd(dimensions) + 1) do
        forged = Interpretation.put(witness, Alloc.row(lay.alloc, {bank.name, row}), column, 999)
        refute Semantics.valid?(pred, forged)
      end

      lay
    end
  end

  @doc "A map shares its rows across seventy steps; forged cells, presence gaps and a walk ended early fail."
  @spec shared_rows() :: Uair.t()
  example shared_rows do
    args = [Enum.to_list(1..70), :_]
    {pred, lay} = laid(doubled(), args, %{0 => [70], 1 => [70]})

    assert [%Alloc.Member{steps: {0, -1}}] =
             Enum.filter(lay.alloc.members, &match?(%Alloc.Member{steps: {_, _}}, &1))

    assert Alloc.width(lay.alloc) == 6

    relation = with_arrays(doubled(), %{0 => [70], 1 => [70]})
    assert Phi.compile(relation) == Phi.compile(relation, nil, args)

    witness = Lay.witness(lay)
    {:ok, uair} = Uair.emit(pred, witness)
    assert Uair.num_cols(uair) == 11
    assert {:ok, %Prover.Report{}, _id} = Prover.prove_uair(uair)

    [%Alloc.Slot{allocation: {:bank, input, _}}, %Alloc.Slot{allocation: {:bank, bank, _}}] =
      Alloc.root(lay.alloc).slots

    row = Alloc.row(lay.alloc, {bank, 1})
    refute Semantics.valid?(pred, Interpretation.put(witness, row, 17, 999))

    refute Semantics.valid?(
             pred,
             Interpretation.put(witness, Alloc.presence(lay.alloc, bank), 17, 0)
           )

    ended =
      Enum.reduce([input, bank], Interpretation.put(witness, row, 71, 999), fn name, forged ->
        Interpretation.put(forged, Alloc.presence(lay.alloc, name), 71, 0)
      end)

    refute Semantics.valid?(pred, ended)

    column = Enum.find_index(uair.rows, &(&1 == row))

    forged = %{
      uair
      | columns: List.update_at(uair.columns, column, &List.replace_at(&1, uair.len - 17, 999))
    }

    assert {:error, {:verifier_rejected, _}} = Prover.prove_uair(forged)
    uair
  end

  @doc "Only aligned tail recursion walks its arrays; other calls keep ordinary compilation."
  @spec walk_boundary() :: [Unfold.key()]
  example walk_boundary do
    walking = fn rel, arrays ->
      root = with_arrays(rel, arrays)
      {:ok, reached} = Program.reached(root, [root])

      for {key = {_name, handed}, _clauses} <-
            Unfold.program(root, Map.new(reached, &{&1.name, &1})),
          Enum.any?(handed, &match?({:bank, _array, _inner}, &1)),
          do: key
    end

    for {rel, arrays} <- [
          {doubled(), %{}},
          {doubled(), %{0 => [2]}},
          {doubled(), %{0 => [2], 1 => [3]}},
          {EUser.doubled_fun(), %{0 => [2], 1 => [4]}},
          {EUser.total(), %{0 => [2]}},
          {EPhi.selected_list(), %{1 => [2], 2 => [2]}}
        ] do
      assert walking.(rel, arrays) == []
    end

    assert [{:doubled, [{:bank, :a1, []}, {:bank, :a2, []}]}] =
             walking.(doubled(), %{0 => [2], 1 => [2]})
  end

  @doc "The array relation rejects ragged values and checks scalar leaves in AL."
  @spec declared_shapes() :: [Zkfol.Refusal.t()]
  example declared_shapes do
    for {dimensions, value} <- [
          {[-1], []},
          {[0, -1], []},
          {[0, []], []},
          {[2, 0, -1], [[], []]},
          {[2], [1]},
          {[2, 2], [[1, 2], [3]]},
          {[2], [[1], [2]]}
        ] do
      assert {:error, {:no_answer, _} = refusal} =
               Al.derived(Zkfol.FOL.array(), [dimensions, value])

      refusal
    end
  end

  @doc "Malformed dimensions have no answer, including improper lists."
  @spec invalid_dimensions() :: [Zkfol.Refusal.t()]
  example invalid_dimensions do
    dimensions = Enum.map([[0, -1], [0, []], [2, 0, -1]], &list_term/1) ++ [{:cons, 0, 1}]

    for dimensions <- dimensions do
      root = %Rel{
        name: :invalid_array,
        arity: 1,
        clauses: [{[{:var, :xs}], [{:call, &Zkfol.FOL.array/0, [dimensions, {:var, :xs}]}]}]
      }

      ran = Zkfol.compile(root, args: [[]])
      assert refusal = {_reason, _detail} = Zkfol.Log.refusal(ran)
      refusal
    end
  end

  @doc "Source declarations survive direct, wrapped, passed and anonymous calls without compile options."
  @spec declared_programs() :: [Lay.t()]
  example declared_programs do
    n = 3

    anonymous =
      rel do
        declared_here(xs, ys) do
          array([^n], xs)
          array([^n], ys)
          doubled(xs, ys)
        end
      end

    for root <- [declared(), wrapped(), passed(), anonymous] do
      {pred, lay} = laid(root, [[1, 2, 3], :_], %{})

      assert [%Alloc.Bank{name: bank}, %Alloc.Bank{}] =
               Enum.filter(lay.alloc.members, &is_struct(&1, Alloc.Bank))

      assert Phi.compile(root) == Phi.compile(root, nil, [[1, 2, 3], :_])
      row = Alloc.row(lay.alloc, {bank, 1})
      refute Semantics.valid?(pred, Interpretation.put(Lay.witness(lay), row, 4, 99))
      lay
    end
  end

  defrel mixed(0, x) do
    x = 7
  end

  defrel mixed(1, x) do
    x = [1, 2]
  end

  defrel mixed_array(0, x) do
    x = 7
  end

  defrel mixed_array(1, x) do
    array([2], x)
    x = [1, 2]
  end

  @doc "One parameter holds a scalar from one clause and a list from the other."
  @spec mixed_parameter() :: [Lay.t()]
  example mixed_parameter do
    shared_parameter(mixed())
  end

  @doc "The list clause declares its array, and the parameter is still shared."
  @spec declared_mixed_parameter() :: [Lay.t()]
  example declared_mixed_parameter do
    shared_parameter(mixed_array())
  end

  # Both answers lay on one compiled predicate, the selector row naming the clause.
  @spec shared_parameter(Rel.t()) :: [Lay.t()]
  defp shared_parameter(root) do
    {:ok, pred, alloc} = Phi.compile(root)
    pred = Alloc.link(pred, alloc)
    [selector] = Alloc.slot_rows(alloc, hd(Alloc.root(alloc).slots))

    for args <- [[0, 7], [1, [1, 2]]] do
      {:ok, derivation} = Al.derived(root, args)
      lay = Lay.of(derivation, alloc)
      witness = Lay.witness(lay)
      assert Semantics.valid?(pred, witness)
      flipped = Interpretation.put(witness, Alloc.row(alloc, selector), 1, 1 - hd(args))
      refute Semantics.valid?(pred, flipped)
      {:ok, claims} = Lay.claims(lay, [1, 2])
      assert {:ok, %Prover.Report{}, _id} = Prover.prove(pred, witness, claims: claims)
      lay
    end
  end

  defrel mixed_map(xs, ys) do
    map(xs, mixed(), ys)
  end

  defrel mixed_array_map(xs, ys) do
    map(xs, mixed_array(), ys)
  end

  @doc "A recursive caller receives scalar and list results through the same parameter."
  @spec mixed_calls() :: [Lay.t()]
  example mixed_calls do
    for root <- [mixed_map(), mixed_array_map()] do
      {_pred, lay} = laid(root, [[0, 1, 0, 1], :_], %{})

      assert Zkfol.Derivation.root(lay.derivation, root.name) ==
               {root.name, [[0, 1, 0, 1], [7, [1, 2], 7, [1, 2]]]}

      lay
    end
  end

  defrel partial_array(xs) do
    xs = [_, 2]
    array([2], xs)
  end

  @doc "A partial list pattern works on either side of the array goal."
  @spec array_goal_order() :: [Lay.t()]
  example array_goal_order do
    root = partial_array()
    [{head, goals}] = root.clauses

    for goals <- [goals, Enum.reverse(goals)] do
      {_pred, lay} = laid(%{root | clauses: [{head, goals}]}, [[1, 2]], %{})
      assert Alloc.width(lay.alloc) == 3
      assert Enum.count(lay.alloc.members, &is_struct(&1, Alloc.Bank)) == 1
      lay
    end
  end

  defrel ordered_array(xs) do
    permutation(2, xs)
    array([n], ys)
    ys = xs
    n = last + 0
    last = 2
  end

  @doc "Declarations resolve aliases and dimensions before consumers, in every goal order."
  @spec declaration_order() :: [Alloc.t()]
  example declaration_order do
    root = ordered_array()
    [{head, goals}] = root.clauses
    ran = Zkfol.compile(root, args: [[1, 2]], public: [1])
    assert %Prover.Report{} = Zkfol.Log.report(ran)

    for ordered <- orders(goals) do
      {:ok, _pred, alloc} = Phi.compile(%{root | clauses: [{head, ordered}]}, nil, [[1, 2]])
      assert Alloc.width(alloc) == 3
      alloc
    end
  end

  defp orders([]), do: [[]]
  defp orders(goals), do: for(goal <- goals, rest <- orders(goals -- [goal]), do: [goal | rest])

  defrel sized_array(n, xs) do
    array([n], xs)
  end

  defrel array_size(n) do
    n = 2
  end

  defrel wrapped_array(xs) do
    xs = [_, 2]
    sized_array(n, xs)
    array_size(n)
  end

  defrel passed_array(xs) do
    xs = [_, 2]
    invoke(sized_array(), n, xs)
    array_size(n)
  end

  @doc "Unconditional and passed wrappers establish the same bank before matching."
  @spec wrapped_declarations() :: [Lay.t()]
  example wrapped_declarations do
    for root <- [wrapped_array(), passed_array()] do
      [{head, goals}] = root.clauses

      for ordered <- orders(goals) do
        {:ok, _pred, alloc} = Phi.compile(%{root | clauses: [{head, ordered}]}, nil, [[1, 2]])
        assert Alloc.width(alloc) == 3
        assert Enum.count(alloc.members, &is_struct(&1, Alloc.Bank)) == 1
      end

      {_pred, lay} = laid(root, [[1, 2]], %{})
      lay
    end
  end

  defrel guarded_array(0, n, xs) do
    n > 2
    array([2], xs)
  end

  defrel guarded_wrapper(tag, n, xs) do
    guarded_array(tag, n, xs)
  end

  @doc "Establishing a wrapper's layout preserves its head and guard constraints."
  @spec declaration_constraints() :: Lay.t()
  example declaration_constraints do
    {pred, lay} = laid(guarded_wrapper(), [0, 3, [1, 2]], %{})
    [tag, n, _xs] = Alloc.root(lay.alloc).slots

    for {slot, forged} <- [{tag, 1}, {n, 2}] do
      [ref] = Alloc.slot_rows(lay.alloc, slot)
      witness = Interpretation.put(Lay.witness(lay), Alloc.row(lay.alloc, ref), 1, forged)
      refute Semantics.valid?(pred, witness)
    end

    lay
  end

  defrel pending_helper(xs, n) do
    array([2], xs)
    permutation(n, xs)
  end

  defrel pending_caller(xs) do
    pending_helper(xs, n)
    length(xs, n)
  end

  @doc "An inlined helper publishes its array while its consumer waits for an outer binding."
  @spec shared_worklist() :: Lay.t()
  example shared_worklist do
    root = pending_caller()
    [{head, goals}] = root.clauses

    {:ok, _pred, alloc} =
      Phi.compile(%{root | clauses: [{head, Enum.reverse(goals)}]}, nil, [[1, 2]])

    assert Alloc.width(alloc) == 3
    {_pred, lay} = laid(root, [[1, 2]], %{})
    assert Alloc.width(lay.alloc) == 3
    lay
  end

  defrel scalar_before_array(xs) do
    natural(xs)
    array([2], xs)
  end

  @doc "An array read as a number is refused."
  @spec conflicting_reads() :: Zkfol.Refusal.t()
  example conflicting_reads do
    root = scalar_before_array()
    assert {:error, {:no_answer, _detail}} = Al.derived(root, [[1, 2]])
    assert {:error, {:unliftable_term, _detail} = reason} = Phi.compile(root)
    reason
  end

  defrel digit_sum([], 0)

  defrel digit_sum([x | xs], s) do
    digit_sum(xs, t)
    s = t + x
  end

  defrel digits(xs, s) do
    array([6], xs)
    each(xs, between(1, 9))
    digit_sum(xs, s)
  end

  @doc "Clearing an array's presence ends no walk early: six digits cannot be made to sum to 6000."
  @spec walks_reach_the_last_element() :: Zkfol.Statement.t()
  example walks_reach_the_last_element do
    rels = [digits(), digit_sum()]
    args = [[4, 2, 9, 3, 5, 7], :_]
    {:ok, derivation} = Al.derived(rels, args)
    {:ok, statement} = Phi.relaid(%Zkfol.Statement{rels: rels, args: args}, derivation)
    alloc = Zkfol.Statement.alloc(statement)
    pred = Zkfol.Statement.pred(statement)
    witness = Zkfol.Statement.witness(statement)
    assert Semantics.valid?(pred, witness)

    [%Alloc.Slot{allocation: {:bank, bank, 6}}, %Alloc.Slot{allocation: {:cell, sum}}] =
      Alloc.root(alloc).slots

    forged =
      Enum.reduce(2..7, Interpretation.put(witness, Alloc.row(alloc, sum), 1, 6000), fn x, w ->
        w
        |> Interpretation.put(Alloc.row(alloc, {bank, 1}), x, 1000)
        |> Interpretation.put(Alloc.presence(alloc, bank), x, 0)
      end)

    refute Semantics.valid?(pred, forged)
    statement
  end

  @spec laid(Rel.t(), [term()], %{non_neg_integer() => [non_neg_integer()]}) ::
          {Ast.pred(), Lay.t()}
  defp laid(rel, args, arrays) do
    rel = with_arrays(rel, arrays)
    {:ok, derivation} = Al.derived(rel, args)
    assert {:ok, pred, alloc} = Phi.compile(rel, nil, args)
    lay = Lay.of(derivation, alloc)
    pred = Alloc.link(pred, alloc)
    assert Semantics.valid?(pred, Lay.witness(lay))
    {pred, lay}
  end

  # Build source goals for the representation comparison; both AL and Phi run this wrapper.
  defp with_arrays(rel, arrays) when map_size(arrays) == 0, do: rel

  defp with_arrays(rel, arrays) do
    args = for i <- 1..rel.arity, do: {:var, :"a#{i}"}

    goals =
      for {i, dimensions} <- Enum.sort(arrays),
          do: {:call, &Zkfol.FOL.array/0, [list_term(dimensions), Enum.at(args, i)]}

    %Rel{
      name: :"array #{rel.name}",
      arity: rel.arity,
      clauses: [{args, goals ++ [{:call, fn -> rel end, args}]}]
    }
  end

  defp list_term([]), do: nil
  defp list_term([x | xs]), do: {:cons, x, list_term(xs)}
end
