defmodule Examples.EArrays do
  @moduledoc "I exercise declared arrays, shared traversal rows and structural matching."
  use ExExample
  use Zkfol
  import ExUnit.Assertions

  alias Zkfol.{Al, Alloc, Array, Ast, Interpretation, Lay, Phi, Prover, Semantics, Uair}
  alias Zkfol.Lang.Rel
  alias Zkfol.Phi.{Place, Traversal, Walk}
  alias Examples.{EAl, EAlloc, EFol, ENodes, EPassed, EPhi, EUser}

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

  defrel diagonal(<<(<<a, _>>), (<<_, d>>)>>, sum) do
    sum = a + d
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
    {_pred, lay, _report} = proved(totals(), [[[1, 2], [4, 5]], :_], %{})
    assert Zkfol.Derivation.root(lay.derivation, :totals) == {:totals, [[[1, 2], [4, 5]], [3, 9]]}
    lay
  end

  @doc "Checking a transposed view's shape reuses the source bank."
  @spec checked_view() :: Lay.t()
  example checked_view do
    {_pred, lay, _report} = proved(checked_transpose(), [[[1, 2, 3], [4, 5, 6]]], %{})
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

    {_pred, lay, _report} = proved(root, [:_], %{})
    lay
  end

  @doc "The same source forms prove with ordinary lists and with declared arrays."
  @spec source_forms() :: [Prover.Report.t()]
  example source_forms do
    cases = [
      {EAlloc.sum(), [3, 4, :_], %{0 => [], 1 => [], 2 => []}},
      {EPhi.equations(), [3, :_], %{}},
      {EPhi.selected_list(), [1, [10, 20, 30], :_], %{1 => [3], 2 => [2]}},
      {EUser.fib(), [8, :_], %{}},
      {EAl.odd(), [5, :_], %{}},
      {EAl.forked(), [3, :_], %{}},
      {doubled(), [[1, 2, 3], :_], %{0 => [3], 1 => [3]}},
      {EUser.both(), [[1, 2, 3], :_], %{0 => [3]}},
      {doubled(), [[1, 2, 3], :_], %{0 => [3]}},
      {EUser.joined(), [[1, 2], [3, 4], :_], %{0 => [2], 1 => [2], 2 => [4]}},
      {ENodes.rev(), [[1, 2, 3], :_], %{0 => [3], 1 => [3]}},
      {EPassed.pick(), [2, [10, 20, 30], :_], %{1 => [3]}},
      {EPassed.first(), [[[10, 20], [30, 40]], :_], %{0 => [2, 2], 1 => [2]}},
      {EPassed.pick(), [2, [[10, 20], [30, 40]], :_], %{1 => [2, 2], 2 => [2]}},
      {EFol.counted(), [[1, 2, 3]], %{0 => [3]}},
      {EFol.bumped(), [:_], %{0 => [3]}},
      {EFol.rising(), [[1, 3, 8]], %{0 => [3]}},
      {EPhi.local_factor(), [6], %{}},
      {EAl.shifty(), [5, 17, :_], %{}},
      {ENodes.same(), [[[[1, 2], [3, 4]], [[5, 6], [7, 8]]], :_],
       %{0 => [2, 2, 2], 1 => [2, 2, 2]}},
      {ENodes.tree(), [[[0, 0], 0], :_], %{}},
      {ENodes.red(), [[[[0, 1], 1], 0], :_], %{}},
      {ENodes.optional_tail(), [0], %{}},
      {EUser.cells_ok(), [[[1, 2], [3, 4]]], %{0 => [2, 2]}},
      {EPhi.counted_construction(), [:_], %{}},
      {EPhi.repeated_calls(), [6, 9], %{}},
      {diagonal(), [[[1, 2], [3, 4]], :_], %{0 => [2, 2]}}
    ]

    for {rel, args, arrays} <- cases, shapes <- Enum.uniq([%{}, arrays]) do
      {_pred, _lay, report} = proved(rel, args, shapes)
      report
    end
  end

  @doc "Empty axes, nested maps, private captures and transposed views preserve source answers."
  @spec composed_traversals() :: [Lay.t()]
  example composed_traversals do
    cases = [
      {doubled(), [[], :_], %{0 => [0], 1 => [0]}, [:doubled]},
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
      {_pred, lay, _report} = proved(rel, args, arrays)

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
      {pred, lay, _report} = proved(ENodes.rev(), [input, :_], %{0 => dimensions})
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

  @doc "A map shares its rows across seventy steps; forged cells and presence gaps fail."
  @spec shared_rows() :: Uair.t()
  example shared_rows do
    args = [Enum.to_list(1..70), :_]
    {pred, lay, _report} = proved(doubled(), args, %{0 => [70], 1 => [70]})

    assert [%Alloc.Member{steps: {0, -1}}] =
             Enum.filter(lay.alloc.members, &match?(%Alloc.Member{steps: {_, _}}, &1))

    assert Alloc.width(lay.alloc) == 6

    relation = with_arrays(doubled(), %{0 => [70], 1 => [70]})
    assert Phi.compile(relation) == Phi.compile(relation, nil, args)

    witness = Lay.witness(lay)
    {:ok, uair} = Uair.emit(pred, witness)
    assert Uair.num_cols(uair) == 9
    [_input, %Alloc.Slot{allocation: {:bank, bank, _}}] = Alloc.root(lay.alloc).slots
    row = Alloc.row(lay.alloc, {bank, 1})
    refute Semantics.valid?(pred, Interpretation.put(witness, row, 17, 999))

    refute Semantics.valid?(
             pred,
             Interpretation.put(witness, Alloc.presence(lay.alloc, bank), 17, 0)
           )

    column = Enum.find_index(uair.rows, &(&1 == row))

    forged = %{
      uair
      | columns: List.update_at(uair.columns, column, &List.replace_at(&1, uair.len - 17, 999))
    }

    assert {:error, {:verifier_rejected, _}} = Prover.prove_uair(forged)
    uair
  end

  @doc "Only aligned tail recursion gets a traversal plan; other calls keep ordinary compilation."
  @spec traversal_boundary() :: Traversal.t()
  example traversal_boundary do
    ref = {:doubled, {:param, :xs}}
    walk = Array.bind(%Array{dimensions: [2]}, ref)
    a = Walk.fetch(walk, ref)

    for {rel, values} <- [
          {doubled(), [[1, 2], [2, 4]]},
          {doubled(), [a, :fresh]},
          {doubled(), [a, Place.shifted(a, -1)]},
          {EUser.doubled_fun(), [a, Place.shifted(a, -2)]},
          {EUser.total(), [a, :fresh]},
          {EPhi.selected_list(), [:fresh, a, a]}
        ] do
      assert Traversal.plan(rel, values) == nil
    end

    plan = Traversal.plan(doubled(), [a, a])
    assert Traversal.call(doubled(), [], plan, plan.edge) == Ast.address(:x, 1, -1)
    assert Traversal.call(doubled(), [:fresh, :fresh], plan, [0 | plan.edge]) == nil
    plan
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

  @doc "Malformed dimensions return a typed lowering refusal, including improper lists."
  @spec invalid_dimensions() :: [Zkfol.Refusal.t()]
  example invalid_dimensions do
    dimensions = Enum.map([[0, -1], [0, []], [2, 0, -1]], &list_term/1) ++ [{:cons, 0, 1}]

    for dimensions <- dimensions do
      root = %Rel{
        name: :invalid_array,
        arity: 1,
        clauses: [{[{:var, :xs}], [{:call, &Zkfol.FOL.array/0, [dimensions, {:var, :xs}]}]}]
      }

      assert {:error, {:array_shape, _} = refusal} = Phi.compile(root)
      ran = Zkfol.compile(root, args: [[]])
      assert {_reason, _detail} = Zkfol.Log.refusal(ran)
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
      {pred, lay, _report} = proved(root, [[1, 2, 3], :_], %{})

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

  @doc "Alternatives share parameter storage for both scalar and list answers."
  @spec mixed_parameters() :: [Lay.t()]
  example mixed_parameters do
    for root <- [mixed(), mixed_array()],
        clauses <- [root.clauses, Enum.reverse(root.clauses)],
        args <- [[0, 7], [1, [1, 2]]] do
      root = %{root | clauses: clauses}
      {:ok, pred, alloc} = Phi.compile(root)
      {:ok, derivation} = Al.derived(root, args)
      lay = Lay.of(derivation, alloc)
      witness = Lay.witness(lay)
      pred = Alloc.link(pred, alloc)
      assert Semantics.valid?(pred, witness)
      [selector] = Alloc.slot_rows(alloc, hd(Alloc.root(alloc).slots))

      refute Semantics.valid?(
               pred,
               Interpretation.put(witness, Alloc.row(alloc, selector), 1, 1 - hd(args))
             )

      {:ok, claims} = Lay.claims(lay, [1, 2])
      assert {:ok, %Prover.Report{}, _id} = Prover.prove(pred, witness, claims: claims)
      ran = Zkfol.compile(root, args: args, public: [1, 2])
      assert %Prover.Report{} = Zkfol.Log.report(Zkfol.Log.snapshot(), ran)
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
      {_pred, lay, _report} = proved(root, [[0, 1, 0, 1], :_], %{})

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
      root = %{root | clauses: [{head, goals}]}
      {_pred, lay, _report} = proved(root, [[1, 2]], %{})
      assert Alloc.width(lay.alloc) == 3
      assert Enum.count(lay.alloc.members, &is_struct(&1, Alloc.Bank)) == 1
      ran = Zkfol.compile(root, args: [[1, 2]], public: [1])
      assert %Prover.Report{} = Zkfol.Log.report(Zkfol.Log.snapshot(), ran)
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
  @spec declaration_order() :: [Lay.t()]
  example declaration_order do
    root = ordered_array()
    [{head, goals}] = root.clauses
    ran = Zkfol.compile(root, args: [[1, 2]], public: [1])
    assert %Prover.Report{} = Zkfol.Log.report(ran)

    for ordered <- orders(goals) do
      root = %{root | clauses: [{head, ordered}]}
      {_pred, lay, _report} = proved(root, [[1, 2]], %{})
      assert Alloc.width(lay.alloc) == 3
      lay
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
    for root <- [wrapped_array(), passed_array()],
        {head, goals} <- root.clauses,
        ordered <- orders(goals) do
      root = %{root | clauses: [{head, ordered}]}
      {_pred, lay, _report} = proved(root, [[1, 2]], %{})
      assert Alloc.width(lay.alloc) == 3
      assert Enum.count(lay.alloc.members, &is_struct(&1, Alloc.Bank)) == 1
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
    {pred, lay, _report} = proved(guarded_wrapper(), [0, 3, [1, 2]], %{})
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
  @spec shared_worklist() :: [Lay.t()]
  example shared_worklist do
    root = pending_caller()
    [{head, goals}] = root.clauses

    for goals <- [goals, Enum.reverse(goals)] do
      root = %{root | clauses: [{head, goals}]}
      {_pred, lay, _report} = proved(root, [[1, 2]], %{})
      assert Alloc.width(lay.alloc) == 3
      lay
    end
  end

  defrel scalar_before_array(xs) do
    natural(xs)
    array([2], xs)
  end

  defrel arithmetic_before_array(xs) do
    y = xs + 0
    array([2], xs)
    y = 1
  end

  @doc "Scalar reads wait for representation; an array cannot leave a dangling scalar row."
  @spec conflicting_reads() :: [Zkfol.Refusal.t()]
  example conflicting_reads do
    for root <- [scalar_before_array(), arithmetic_before_array()] do
      assert {:error, {:no_answer, _detail}} = Al.derived(root, [[1, 2]])
      assert {:error, {:unliftable_term, _detail} = reason} = Phi.compile(root)
      reason
    end
  end

  @spec proved(Rel.t(), [term()], %{non_neg_integer() => [non_neg_integer()]}) ::
          {Ast.pred(), Lay.t(), Prover.Report.t()}
  defp proved(rel, args, arrays) do
    rel = with_arrays(rel, arrays)
    {:ok, derivation} = Al.derived(rel, args)
    assert {:ok, pred, alloc} = Phi.compile(rel, nil, args)
    lay = Lay.of(derivation, alloc)
    witness = Lay.witness(lay)
    pred = Alloc.link(pred, alloc)
    assert Semantics.valid?(pred, witness)
    {:ok, claims} = Lay.claims(lay, Enum.to_list(1..rel.arity))
    assert {:ok, report, _id} = Prover.prove(pred, witness, claims: claims)
    {pred, lay, report}
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
