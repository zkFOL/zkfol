defmodule Zkfol.Unrolling do
  @moduledoc """
  I decide where each list stands so that the predicate reads it without a pointer.

  Zinc+ charges for pointer reads. A list laid along the trace, one element per column
  with its head at a column affine in X, is read by plain shifts instead. I choose that
  layout wherever the relation's clauses allow it: a cons becomes cells one column apart,
  a recursive call becomes the same member one column back, and a call over a source
  literal is replaced by its clauses. This is an optimization. With `unrolling: false` on
  the `Zkfol.Phi` pass, Phi does not call me: every list is a node in the heap, every
  constant a count in its cell, every call a member at a pointer, and every program
  still compiles and proves at a higher cost. If pricing moves to egglog, or a backend
  makes pointer reads cheap, this module is what changes.

  Per member, before any clause is matched, I compute the stepping call, which is the
  first call that moves a parameter; the column counter, which is the parameter
  that call moves or else the first list, whose count is read from the column; the extent
  of every other list relative to that counter; and a place for each parameter, by the
  table in `place/6`.

  An affine extent is a candidate until every alternative clause establishes it. Its
  equation is `length = m * n + b`, where `n` is the source counter parameter. A closed
  head anchors its length; a call substitutes its source arguments into that equation.
  Only `parameters/6` translates between these lengths and physical columns.
  Unknown or disagreeing evidence leaves a list open for node storage. This analysis
  reads heads and calls; it does not execute body equations to discover more shapes.

  Per call, I decide whether it is unrolled into its clauses or compiled as a member
  (`strategy/4`), and the column a continued or a new member stands at (`frame/2`).

  ### Public API

  - `column/3`: choose the stepping call and column counter.
  - `parameters/6`: a shape and a place per parameter, in the chosen column.
  - `strategy/4`: unroll a call, prefer a member, or require one.
  - `frame/2`: locate a call from its column counter.
  """

  use TypedStruct

  alias Zkfol.Alloc.Bank
  alias Zkfol.Ast
  alias Zkfol.Lang
  alias Zkfol.Lang.Rel
  alias Zkfol.Phi.{Layout, Place, Shape, Value}

  require Place

  @typedoc "The column counter: which parameter, and its value at column zero."
  @type counter :: {non_neg_integer(), integer()}

  @typedoc """
  The stepping call: which parameter it moves, by how much, and the source clause and
  call establishing that movement. Extent analysis reads these same source terms.
  """
  @type step :: {non_neg_integer(), integer(), clause(), term()}

  @typedoc "The stepping call and column counter chosen before entering a member's frame."
  typedstruct do
    field(:step, step() | nil)
    field(:counter, counter() | nil)
  end

  @typep clause :: {[term()], [term()]}
  @typep clauses :: [clause()]

  @typep length_rule ::
           {:head, integer() | nil, integer() | nil}
           | {:step, integer() | nil, integer() | nil}
           | {:extent, Shape.extent() | nil}

  # Extents here are functions of the source parameter, not of the physical column X.
  # Only inherited list lengths enter the analysis; places and banks stay at its boundary.
  @typep solve :: %{
           step: step() | nil,
           parameter: non_neg_integer() | nil,
           extents: %{non_neg_integer() => Shape.extent()},
           scope: %{atom() => Rel.t()},
           seen: [atom()]
         }

  @doc """
  I choose the stepping call and column counter: the parameter the call displaces,
  or else the first counted argument. A scalar needs a lower bound from the clauses;
  otherwise it stays in a cell. A heap term cannot count the column.
  `handed` contains canonical values from `Value.handed/1`. This choice determines
  the call's frame and is retained when its arguments move into that frame.
  Parameter extents are inferred after that move.
  """
  @spec column(Rel.t(), [Place.t()], Place.known()) :: t()
  def column(rel = %Rel{clauses: clauses}, handed, known) do
    step = displaced_call(clauses)
    j = (step && elem(step, 0)) || Enum.find_index(handed, &counted?(&1, known))

    counter =
      with j when j != nil <- j,
           false <- term?(clauses, j),
           form = Enum.at(handed, j),
           true <- walkable?(form),
           origin when is_integer(origin) <- origin(rel, j, Place.shape(form, known)) do
        {j, origin}
      else
        _unsupported -> nil
      end

    %__MODULE__{step: step, counter: counter}
  end

  @doc """
  I return a shape and a place per parameter. The arguments are expressed in the
  callee's frame; the column is the choice that located that frame.
  """
  @spec parameters(
          Rel.t(),
          [Ast.row_ref()],
          [Place.t()],
          Place.known(),
          %{atom() => Rel.t()},
          t()
        ) :: {[Shape.t()], [Place.t()]}
  def parameters(rel = %Rel{clauses: clauses, arity: arity}, refs, handed, known, scope, column) do
    %__MODULE__{step: step, counter: counter} = column
    {parameter, origin} = counter || {nil, 0}

    extents =
      for {form, k} <- Enum.with_index(handed),
          {:list, extent, _element} <- [Place.shape(form, known)],
          into: %{},
          do: {k, Shape.from(extent, -origin)}

    solve = %{
      step: step,
      parameter: parameter,
      extents: extents,
      scope: scope,
      seen: [rel.name]
    }

    shapes =
      for k <- 0..(arity - 1)//1 do
        case extent(rel, k, solve) do
          nil -> :scalar
          extent -> {:list, Shape.from(extent, origin), Layout.element(Enum.at(handed, k), known)}
        end
      end

    places =
      for {{ref, form, shape}, k} <- Enum.with_index(Enum.zip([refs, handed, shapes])) do
        place(clauses, k, ref, form, shape, column)
      end

    {shapes, places}
  end

  # A term, a list whose extent cannot follow the member's column, and an unbounded
  # list nothing was handed for use nodes. A scalar is a cell, except the column
  # counter, which reads the column itself, and a handed constant, which is inlined. A
  # passed relation's fixed arguments take the member's own cells. A list that already
  # stands somewhere is read where it is, re-headed at the member's extent when the member
  # steps. Every other list takes a bank along the trace.
  @spec place(clauses(), integer(), Ast.row_ref(), Place.t(), Shape.t(), t()) :: Place.t()
  defp place(clauses, k, ref, form, shape, %__MODULE__{step: step, counter: counter}) do
    {j, o} = counter || {nil, 0}

    cond do
      Enum.any?([
        term?(clauses, k),
        match?({:node, _}, form),
        not Layout.matrix?(form),
        step != nil and counter == nil and shape != :scalar,
        open?(shape) and (Place.fresh?(form) or step != nil)
      ]) ->
        {:node, Ast.cell(ref)}

      shape == :scalar and k == j ->
        Ast.add(:x, o)

      match?({:rel, _, _}, form) ->
        Place.owned(form, ref)

      shape == :scalar ->
        scalar_place(form, ref)

      Place.is_laid(form) and step != nil and counter != nil ->
        Place.stepped(form, shape)

      match?({:across, _, _, _}, form) or Place.is_laid(form) or match?({:pair, _, _}, form) ->
        form

      true ->
        {:along, {Bank.of(ref), 1}, Place.head(shape)}
    end
  end

  @spec open?(Shape.t()) :: boolean()
  defp open?({:list, {:at_least, _}, _}), do: true
  defp open?(_shape), do: false

  @spec scalar_place(Place.t(), Ast.row_ref()) :: Place.t()
  defp scalar_place(q, _ref) when is_integer(q), do: q
  defp scalar_place({:count, q, _cell}, ref), do: {:count, q, Ast.cell(ref)}
  defp scalar_place(:fresh, ref), do: {:fresh, ref}
  defp scalar_place(form, _ref), do: form

  ############################################################
  #                       The counter                        #
  ############################################################

  # A position that is an integer in one head and a bracket in another: a term of two
  # constructors, which only the heap holds.
  @spec term?(clauses(), non_neg_integer()) :: boolean()
  defp term?(clauses, k) do
    heads = for {head, _body} <- clauses, do: Enum.at(head, k)
    Enum.any?(heads, &is_integer/1) and Enum.any?(heads, &Lang.Term.sequence?/1)
  end

  # A list, or a scalar that moves with the column.
  @spec counted?(Place.t(), Place.known()) :: boolean()
  defp counted?(place, known) do
    case {place, Place.shape(place, known)} do
      {_place, {:list, _extent, _element}} -> true
      {term, :scalar} -> match?({m, _a} when m != 0, Place.affine(term))
      _other -> false
    end
  end

  # A node or a pair is read through the heap.
  @spec walkable?(Place.t()) :: boolean()
  defp walkable?({:node, _}), do: false
  defp walkable?({:pair, _, _}), do: false
  defp walkable?(_place), do: true

  # The first call that moves a parameter.
  @spec displaced_call(clauses()) :: step() | nil
  defp displaced_call(clauses) do
    Enum.find_value(clauses, fn clause = {head, body} ->
      Enum.find_value(body, fn
        call = {:call, q, args} when is_atom(q) ->
          Enum.find_value(Enum.with_index(head), fn {pattern, k} ->
            shifts = Enum.map(args, &displaced(&1, pattern))

            with c when c not in [nil, 0] <- Enum.find(shifts, &(&1 not in [nil, 0])),
                 do: {k, c, clause, call}
          end)

        _goal ->
          nil
      end)
    end)
  end

  # How far an argument is displaced from a head pattern: `x - 1` from `x` is -1, the
  # tail from `[h | t]` is -1, the pattern itself is 0.
  @spec displaced(term(), term()) :: integer() | nil
  defp displaced(name = {:var, _}, name) do
    0
  end

  defp displaced({:add, a, q}, pattern) when is_integer(q) do
    with c when is_integer(c) <- displaced(a, pattern), do: c + q
  end

  defp displaced({:cons, h, rest}, {:cons, h, t}) do
    displaced(rest, t)
  end

  defp displaced(arg, {:cons, _, t}) do
    with c when is_integer(c) <- displaced(arg, t), do: c - 1
  end

  defp displaced(_arg, _pattern) do
    nil
  end

  # List origins use lengths from the heads and the handed shape. A scalar needs
  # a source lower bound: literal anchors, and a required self call to an equal or
  # smaller value in every other clause. A private scalar never chooses an origin.
  @spec origin(Rel.t(), non_neg_integer(), Shape.t()) :: integer() | nil
  defp origin(rel = %Rel{clauses: clauses}, j, shape) do
    heads = for {head, _body} <- clauses, do: Enum.at(head, j)
    list? = match?({:list, _, _}, shape) or Enum.all?(heads, &Lang.Term.sequence?/1)

    if list? do
      lengths = for {head, _body} <- clauses, n = count_in(head, j), do: n
      Enum.min([1 | lengths ++ List.wrap(Shape.count(shape))]) - 1
    else
      scalar_origin(rel, j)
    end
  end

  @spec scalar_origin(Rel.t(), non_neg_integer()) :: integer() | nil
  defp scalar_origin(%Rel{name: name, clauses: clauses}, j) do
    anchors = for {head, _body} <- clauses, n = Enum.at(head, j), is_integer(n), do: n

    bounded =
      Enum.all?(clauses, fn {head, body} ->
        parameter = Enum.at(head, j)

        is_integer(parameter) or
          (match?({:var, _}, parameter) and
             Enum.any?(body, fn
               {:call, ^name, args} ->
                 match?(d when is_integer(d) and d <= 0, displaced(Enum.at(args, j), parameter))

               _goal ->
                 false
             end))
      end)

    if anchors != [] and bounded, do: Enum.min([1 | anchors]) - 1
  end

  # The count a head pattern fixes for a parameter: the integer, the length of a closed
  # bracket, nothing for a name or an open bracket.
  @spec count_in([term()], non_neg_integer()) :: integer() | nil
  defp count_in(head, k) do
    case Enum.at(head, k) do
      q when is_integer(q) ->
        q

      bracket ->
        with elements when elements != nil <- Lang.Term.closed(bracket), do: length(elements)
    end
  end

  ############################################################
  #                        The extents                       #
  ############################################################

  # A list parameter's extent, from the recurrence alone; nil for a parameter that is no
  # list. Without a counter a list keeps the extent it came with, or is open.
  @spec extent(Rel.t(), non_neg_integer(), solve()) :: Shape.extent() | nil
  defp extent(rel = %Rel{clauses: clauses}, k, solve) do
    inherited = Map.get(solve.extents, k)
    list? = inherited != nil or Layout.list?(clauses, k)

    cond do
      not list? -> nil
      solve.step == nil or solve.parameter == nil -> inherited || {:at_least, 0}
      k == solve.parameter -> {1, 0}
      true -> recurrence_extent(rel, k, solve)
    end
  end

  # A clause supports a length equation through its head or one required call.
  # A head gives (counter, length); a step gives their changes at the same parameter
  # positions. Only the selected foreign call supplies a callee equation, once.
  # The selected movement proposes a rate; every clause must support its equation.
  @spec recurrence_extent(Rel.t(), non_neg_integer(), solve()) :: Shape.extent()
  defp recurrence_extent(rel, k, solve) do
    {j, dc, selected, call = {:call, callee, args}} = solve.step

    {head, _body} = selected

    proposal =
      if callee == rel.name,
        do: {:step, dc, displaced(Enum.at(args, k), Enum.at(head, k))},
        else: {:extent, call_extent(call, head, k, solve)}

    lengths =
      for {i, {0, length}} <- solve.extents, carried?(rel, i), into: %{}, do: {i, length}

    clauses =
      for clause = {head, body} <- rel.clauses do
        if clause == selected and callee != rel.name do
          [proposal]
        else
          calls =
            for {:call, name, args} <- body, name == rel.name do
              {:step, displaced(Enum.at(args, j), Enum.at(head, j)),
               displaced(Enum.at(args, k), Enum.at(head, k))}
            end

          [{:head, count_in(head, j), head_count(head, k, lengths)} | calls]
        end
      end

    inherited = Map.get(solve.extents, k, {:at_least, 0})

    with extent = {m, _b} when is_integer(m) <- candidate_extent(proposal, clauses, inherited),
         true <- Enum.all?(clauses, fn rules -> Enum.any?(rules, &supports?(&1, extent)) end) do
      extent
    else
      _unknown -> {:at_least, 0}
    end
  end

  @spec candidate_extent(length_rule(), [[length_rule()]], Shape.extent()) :: Shape.extent() | nil
  defp candidate_extent({:extent, extent}, _clauses, _inherited), do: extent

  defp candidate_extent({:step, dc, dl}, clauses, inherited) do
    if is_integer(dl) and rem(dl, dc) == 0 do
      rate = div(dl, dc)

      Enum.find_value(clauses, fn
        [{:head, n, length} | _calls] when is_integer(n) and is_integer(length) ->
          {rate, length - rate * n}

        _unknown ->
          nil
      end)
    else
      inherited
    end
  end

  @spec supports?(length_rule(), {integer(), integer()}) :: boolean()
  defp supports?({:head, n, length}, {rate, offset})
       when is_integer(n) and is_integer(length),
       do: length == rate * n + offset

  defp supports?({:head, nil, length}, {0, offset}) when is_integer(length),
    do: length == offset

  defp supports?({:step, dc, dl}, {rate, _offset})
       when is_integer(dc) and is_integer(dl),
       do: dl == rate * dc

  defp supports?({:extent, extent}, extent), do: true
  defp supports?(_rule, _extent), do: false

  # Substitute the source arguments in the callee's established extent. Its counter
  # may occupy a different argument position; no physical columns enter this equation.
  @spec call_extent(term(), [term()], non_neg_integer(), solve()) :: Shape.extent() | nil
  defp call_extent({:call, q, args}, head, k, solve) do
    with callee = %Rel{} <- solve.scope[q],
         false <- q in solve.seen,
         step = {jc, _delta, _clause, _call} <- displaced_call(callee.clauses),
         false <- term?(callee.clauses, jc),
         dc when is_integer(dc) <- displaced(Enum.at(args, jc), Enum.at(head, solve.parameter)),
         {p, dn} <-
           Enum.find_value(Enum.with_index(args), fn {arg, p} ->
             with dn when is_integer(dn) <- displaced(arg, Enum.at(head, k)), do: {p, dn}
           end),
         false <- term?(callee.clauses, p),
         inner = %{solve | step: step, parameter: jc, extents: %{}, seen: [q | solve.seen]},
         extent = {m, _b} when is_integer(m) <- extent(callee, p, inner) do
      extent |> Shape.from(dc) |> Shape.longer(-dn)
    else
      _unknown -> nil
    end
  end

  # A head fixes a length directly, or shares a name with an argument of known length.
  @spec head_count([term()], non_neg_integer(), %{non_neg_integer() => integer()}) ::
          integer() | nil
  defp head_count(head, k, lengths) do
    count_in(head, k) ||
      Enum.find_value(Enum.with_index(head), fn {pattern, i} ->
        if match?({:var, _}, pattern) and pattern == Enum.at(head, k), do: lengths[i]
      end)
  end

  # A handed length is local to this member. Until call cycles are analyzed, only
  # direct self calls can inherit it; each must pass this argument unchanged.
  @spec carried?(Rel.t(), non_neg_integer()) :: boolean()
  defp carried?(%Rel{name: name, clauses: clauses}, i) do
    Enum.all?(clauses, fn {head, body} ->
      Enum.all?(body, fn
        {:call, ^name, args} -> Enum.at(args, i) == Enum.at(head, i)
        {:call, _callee, _args} -> false
        _goal -> true
      end)
    end)
  end

  ############################################################
  #                         The calls                        #
  ############################################################

  @typedoc """
  The argument sizes of every call being unrolled on the path, by call, so a recursive
  call can be seen to shrink or not.
  """
  @type inlining :: %{{atom(), [{non_neg_integer(), Value.t()}]} => [integer() | nil]}

  @doc """
  I decide whether a recursive call is unrolled into its clauses, prefers a member, or
  must be a member. It is unrolled only while no known argument size grows or appears and
  one shrinks, which bounds the unrolling. A call over a counted list prefers a member. I
  also return the updated sizes for the path.
  """
  @spec strategy(Rel.t(), [Value.t()], Place.known(), inlining()) ::
          {:inline | :prefer_call | :residual, inlining()}
  def strategy(%Rel{name: name}, values, known, inlining) do
    key = specialization(name, values)
    sizes = Enum.map(values, &size(&1, known))
    around = Map.get(inlining, key)
    shrunk = if around, do: Enum.zip(sizes, around)
    constructed = Enum.any?(values, &(is_list(&1) or match?({:pair, _, _}, &1)))

    decreases =
      shrunk == nil or
        (Enum.all?(shrunk, fn {a, b} -> a == nil or (b != nil and a <= b) end) and
           Enum.any?(shrunk, fn {a, b} -> a != nil and b != nil and a < b end))

    strategy =
      cond do
        not decreases ->
          :residual

        not constructed and Enum.any?(values, &(Place.count(&1) != nil)) ->
          :prefer_call

        true ->
          :inline
      end

    {strategy, Map.put(inlining, key, sizes)}
  end

  # Two calls with different passed relations are different calls for the shrinking check.
  @spec specialization(atom(), [Value.t()]) :: {atom(), [{non_neg_integer(), Value.t()}]}
  defp specialization(name, values),
    do: {name, for({value = {:rel, _, _}, k} <- Enum.with_index(values), do: {k, value})}

  # How many cells a value holds, a natural standing for that many and an unresolved
  # scalar for one; a negative or an element of unknown shape counts nothing.
  @spec size(Value.t(), Place.known()) :: non_neg_integer() | nil
  defp size(q, _known) when is_integer(q), do: if(q >= 0, do: q)
  defp size(laid, known) when Place.is_laid(laid), do: Place.size(laid, known)
  defp size([], _known), do: 0

  defp size({:pair, h, t}, known),
    do: with(a when a != nil <- size(h, known), b when b != nil <- size(t, known), do: a + b)

  defp size([h | t], known),
    do: with(a when a != nil <- size(h, known), b when b != nil <- size(t, known), do: a + b)

  defp size({:across, _, _, _}, _known), do: nil
  defp size({:rel, _p, _f}, _known), do: nil
  defp size(_cell, _known), do: 1

  @doc """
  I locate the callee's counter in the caller's column, or use a pointer when that
  count is unknown. A new member without a counter shares the caller's column.
  """
  @spec frame([Value.t()], counter() | nil) :: Ast.address() | :ptr
  def frame(_values, nil), do: Ast.address(:x, 1, 0)

  def frame(values, {j, o}) do
    count =
      case Enum.at(values, j) do
        laid when Place.is_laid(laid) -> Place.extent(laid)
        cells when is_list(cells) -> if Layout.data?(cells), do: {0, length(cells)}
        form -> Place.affine(form)
      end

    with {m, a} <- count, do: Ast.address(:x, m, a - o), else: (_open -> :ptr)
  end
end
