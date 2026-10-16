defmodule Zkfol.Face do
  @moduledoc "I am the system shaped for a viewer: plain maps and strings a GUI renders."

  use GtBridge.View

  alias GtBridge.Phlow.ColumnedList
  alias GtBridge.Phlow.Mondrian
  alias Zkfol.Ast
  alias Zkfol.Interpretation
  alias Zkfol.Lang
  alias Zkfol.Semantics
  alias Zkfol.Log
  alias Zkfol.Refusal
  alias Zkfol.Statement
  alias Zkfol.Statement.Solved
  alias Zkfol.Uair
  alias Zkfol.ZincPlus

  @doc "I am a relation shaped for its clauses view: each clause as the surface writes it."
  @spec rel(Lang.Rel.t()) :: %{atom() => term()}
  def rel(%Lang.Rel{name: name, arity: arity, clauses: clauses}) do
    %{arity: arity, clauses: for({head, body} <- clauses, do: clause_text(name, head, body))}
  end

  @doc "I am a relation's compiled shape, or why it refuses."
  @spec shape(Lang.Rel.t()) :: %{atom() => term()}
  def shape(rel = %Lang.Rel{}) do
    case Zkfol.Phi.compile(rel) do
      {:ok, pred, alloc} ->
        %{
          members: Zkfol.Alloc.names(alloc),
          regions: for({sym, width} <- Zkfol.Alloc.regions(alloc), do: "#{sym} #{width}"),
          rows: Zkfol.Alloc.width(alloc),
          branches: length(Ast.branches(pred))
        }

      {:error, refusal} ->
        %{refused: Refusal.message(refusal)}
    end
  end

  @doc "I am the statement's facts, one map: what a delta view compares."
  @spec summary(Statement.t()) :: %{atom() => term()}
  def summary(statement = %Statement{}) do
    pred = if match?(%Statement{stage: %Solved{}}, statement), do: Statement.pred(statement)

    %{
      rels: length(statement.rels),
      branches:
        if(pred,
          do: pred |> Ast.conjuncts() |> Enum.map(&Ast.branches/1) |> List.flatten() |> length()
        ),
      arity: if(match?([_root | _rest], statement.rels), do: hd(statement.rels).arity),
      witness: if(pred, do: "#{length(Interpretation.rows(Statement.witness(statement)))} rows"),
      claims: length(Statement.claims(statement)),
      args: statement.args
    }
  end

  @doc "I am the statement as diffable text, pretty, bounded."
  @spec text(Statement.t()) :: String.t()
  def text(statement = %Statement{}), do: inspected(statement)

  @doc "I am the derivation shaped for its view: one row per fact, what it consumed, its fan-in."
  @spec derivation(Statement.t() | Zkfol.Derivation.t() | nil) :: %{atom() => term()}
  def derivation(statement = %Statement{}), do: derivation(Statement.derivation(statement))

  def derivation(d = %Zkfol.Derivation{}) do
    consumption = Zkfol.Derivation.consumption(d)
    fans = consumption |> Enum.flat_map(&elem(&1, 1)) |> Enum.frequencies()

    %{
      rows:
        for {fact, used} <- consumption do
          %{
            fact: fact_row(fact),
            label: fact_label(fact_row(fact)),
            consumes: Enum.map(used, &fact_row/1),
            fan_in: Map.get(fans, fact, 0)
          }
        end
    }
  end

  def derivation(nil), do: %{rows: []}

  @spec fact_row(Zkfol.Derivation.fact()) :: [term()]
  defp fact_row({name, tuple}), do: [name | tuple]

  @doc "I am the judgement as a table: a row per branch, a column per witness column."
  @judgement_keys ~w(holds labels evals terms trees sources rows regions arrows aims witness)a

  @spec judgement(Statement.t()) :: %{atom() => term()}
  def judgement(statement = %Statement{stage: %Solved{lay: lay}}) do
    witness = Statement.witness(statement)

    branches =
      statement |> Statement.pred() |> Ast.conjuncts() |> Enum.flat_map(&Ast.branches/1)

    len = Interpretation.len(witness)
    conjuncts = Enum.map(branches, &conjuncts_of/1)

    Map.merge(lay(lay), %{
      holds: for(x <- 1..len, do: Semantics.holds?(Statement.pred(statement), witness, x)),
      labels: labels(statement, length(branches)),
      evals: for(b <- branches, do: for(x <- 1..len, do: Semantics.eval(b, witness, x))),
      terms: for(goals <- conjuncts, do: Enum.map(goals, &phi_text/1)),
      trees:
        for goals <- conjuncts do
          for x <- 1..len, do: for(g <- goals, do: tree(g, witness, x))
        end,
      sources: sources(statement, length(branches))
    })
  end

  def judgement(%Statement{}), do: Map.new(@judgement_keys, &{&1, []})

  @doc "I am the lay's join for its picture: the facts its stands reach, the sites, the stands."
  @spec stands(Zkfol.Lay.t()) :: %{atom() => term()}
  def stands(lay = %Zkfol.Lay{stands: stands, alloc: alloc, derivation: derivation}) do
    sites =
      for %Zkfol.Alloc.Member{name: name, sites: sites} <- alloc.members,
          do: {name, sites |> Map.values() |> Enum.concat() |> Enum.uniq()}

    reached = MapSet.new(for s <- stands, f <- [s.fact | for({_site, u} <- s.uses, do: u)], do: f)

    drawn =
      for {fact, index} <- Enum.with_index(derivation.facts),
          MapSet.member?(reached, fact),
          do: {fact, index}

    at = Map.new(Enum.with_index(drawn), fn {{fact, _source}, index} -> {fact, index} end)

    {rows, []} =
      Enum.map_reduce(stands, Zkfol.Lay.arrows(lay), fn stand, arrows ->
        {mine, rest} = Enum.split(arrows, length(stand.uses))

        uses =
          for {{site, fact}, arrow} <- Enum.zip(stand.uses, mine),
              do: use(stand.member, site, at[fact], arrow, sites)

        row = %{
          fact: at[stand.fact],
          member: stand.member,
          laid: "X = #{stand.column}",
          uses: uses
        }

        {row, rest}
      end)

    %{
      facts: for({fact, index} <- drawn, do: %{index: index, label: fact_label(fact_row(fact))}),
      members: for({name, ss} <- sites, do: %{name: name, sites: Enum.map(ss, &site_text/1)}),
      stands: rows
    }
  end

  # A site stands among the sites of the member whose clause makes the call, not the callee's.
  @spec use(atom(), Zkfol.Alloc.Site.t(), non_neg_integer(), map(), keyword()) ::
          %{atom() => term()}
  defp use(member, site = %Zkfol.Alloc.Site{}, fact, arrow, sites),
    do: %{
      fact: fact,
      site: [member, Enum.find_index(sites[member], &(&1 == site))],
      laid: "X = #{arrow.to}"
    }

  @spec site_text(Zkfol.Alloc.Site.t()) :: String.t()
  defp site_text(%Zkfol.Alloc.Site{callee: callee, address: address}),
    do: "#{callee} at #{term_text(Ast.naming(address))}"

  @doc "I am one lay for its grid: row labels, the matrix by column, regions, arrows, aims."
  @spec lay(Zkfol.Lay.t()) :: %{atom() => term()}
  def lay(lay = %Zkfol.Lay{}) do
    %{
      rows: lay_labels(lay),
      regions: Zkfol.Lay.regions(lay),
      arrows: Zkfol.Lay.arrows(lay),
      aims: Zkfol.Lay.addresses(lay),
      witness: matrix(lay)
    }
  end

  @spec matrix(Zkfol.Lay.t()) :: [[integer()]]
  defp matrix(lay) do
    witness = Zkfol.Lay.witness(lay)

    for x <- 1..Interpretation.len(witness) do
      for i <- 1..length(Interpretation.rows(witness)), do: Interpretation.at(witness, i, x)
    end
  end

  @spec lay_labels(Zkfol.Lay.t()) :: [String.t()]
  defp lay_labels(%Zkfol.Lay{alloc: alloc}) do
    for {ref, r} <- Enum.with_index(Zkfol.Alloc.refs(alloc), 1), do: "C#{r} · #{row_text(ref)}"
  end

  @spec row_text(Ast.row_ref()) :: String.t()
  defp row_text({:in, name}), do: "in #{name}"
  defp row_text({name, {:param, sym}}), do: "#{name} #{sym}"
  defp row_text({name, {:own, {sym, _site}}}), do: "#{name} #{sym}"
  defp row_text({name, i}), do: "#{name} #{inspect(i)}"

  @doc "I am the emitted UAIR for its grid, every row's kind named."
  @spec grid(Uair.t()) :: %{atom() => term()}
  def grid(uair = %Uair{}) do
    reads = mode_feed(uair.mode)

    %{
      columns: uair.columns,
      len: uair.len,
      num_vars: uair.columns |> hd() |> length() |> then(&round(:math.log2(&1))),
      num_public: uair.num_public,
      degree: uair.degree,
      shifts: Enum.map(uair.shifts, &Tuple.to_list/1),
      reads: reads,
      kinds: kinds(uair.rows, reads, uair.shifts, uair.limbs),
      origins: Enum.map(uair.rows, &origin_text/1)
    }
  end

  @doc "I am the pinned code's parameters, asked of the backend."
  @spec pcs() :: ZincPlus.pcs_params()
  def pcs, do: ZincPlus.pcs_params()

  @spec origin_text(pos_integer() | :x | :ones) :: String.t()
  defp origin_text(:x), do: "x"
  defp origin_text(:ones), do: "ones"
  defp origin_text(row), do: "C#{row}"

  @doc "I am the AL program the act ran, on the run's own branch; nil where none is alive."
  @spec program(Log.t(), Log.Run.t() | pos_integer()) :: AL.Object.t() | nil
  def program(snap, %Log.Run{defined: defined}), do: program(snap, defined)

  def program(snap, defined) do
    Enum.find_value(Log.thread(snap, defined), fn
      %Log.Event{body: {:al_solved, %{program: program}}} -> alive(program)
      %Log.Event{} -> nil
    end)
  end

  @spec alive(AL.Object.t()) :: AL.Object.t() | nil
  defp alive(program = %AL.Object{branch: :main}), do: program

  defp alive(program = %AL.Object{branch: branch}) do
    if Enum.any?(AL.Branch.list(), &(&1.id == branch)), do: program
  end

  @doc "I am the route as structure: each pass, its options, its callbacks, its first sentence."
  @spec route(Zkfol.Pipeline.t()) :: %{atom() => term()}
  def route(%Zkfol.Pipeline{passes: passes}) do
    %{
      passes:
        for {{pass, opts}, index} <- Enum.with_index(passes, 1) do
          Code.ensure_loaded(pass)

          %{
            index: index,
            name: pass |> Module.split() |> List.last(),
            module: pass,
            opts: if(opts == [], do: nil, else: inspect(opts)),
            says: first_sentence(pass),
            implements:
              for(
                {name, arity} <- Zkfol.Pipeline.behaviour_info(:callbacks),
                function_exported?(pass, name, arity),
                do: "#{name}/#{arity}"
              )
          }
        end
    }
  end

  @doc "I re-emit the act's final stage as its UAIR, or the refusal's prose."
  @spec emitted(Log.Run.t()) :: Uair.t() | {:refused, String.t()}
  def emitted(ran) do
    final = Log.Run.final_stage(ran)

    case Uair.emit(Statement.pred(final), Statement.witness(final), Statement.claims(final)) do
      {:ok, uair} -> uair
      {:error, refusal} -> {:refused, Refusal.message(refusal)}
    end
  end

  defview derivation_view(statement = %Statement{}, builder) do
    case derivation(statement) do
      %{rows: []} ->
        builder.empty()

      feed ->
        builder.columned_list()
        |> ColumnedList.title("Derivation")
        |> ColumnedList.priority(13)
        |> ColumnedList.items(Enum.with_index(feed.rows, 1))
        |> ColumnedList.send(fn {_row, k} -> Statement.under(statement, k) end)
        |> ColumnedList.column("Fact", fn {row, _k} -> fact_label(row.fact) end)
        |> ColumnedList.column("Consumes", fn {row, _k} ->
          Enum.map_join(row.consumes, "   ", &fact_label/1)
        end)
        |> ColumnedList.column("Fan-in", fn {row, _k} -> to_string(row.fan_in) end)
    end
  end

  @spec fact_label([term()]) :: String.t()
  defp fact_label([name | tuple]), do: "#{name}(#{Enum.map_join(tuple, ", ", &argument_text/1)})"

  @spec argument_text(term()) :: String.t()
  defp argument_text(items) when is_list(items) do
    shown = items |> Enum.take(4) |> Enum.map_join(", ", &argument_text/1)
    cut(if length(items) > 4, do: "[#{shown}, ...]", else: "[#{shown}]")
  end

  defp argument_text(value),
    do: cut(if String.Chars.impl_for(value), do: to_string(value), else: inspect(value))

  # A nested list is a wall: every argument reads at a glance or is cut.
  @spec cut(String.t()) :: String.t()
  defp cut(text), do: if(byte_size(text) > 12, do: String.slice(text, 0, 11) <> "…", else: text)

  defview lowering_view(statement = %Statement{}, builder) do
    case Statement.lowering(statement) do
      nil -> builder.empty()
      walk -> clause_list(walk.clauses, "Lowering", builder)
    end
  end

  defview clauses_view(%Zkfol.Phi.Walk{clauses: clauses}, builder) do
    clause_list(clauses, "Clauses", builder)
  end

  @spec clause_list([Zkfol.Phi.Walk.Clause.t()], String.t(), module()) :: ColumnedList.t()
  defp clause_list(clauses, title, builder) do
    builder.columned_list()
    |> ColumnedList.title(title)
    |> ColumnedList.priority(1)
    |> ColumnedList.items(clauses)
    |> ColumnedList.column("Member", &to_string(&1.member))
    |> ColumnedList.column("Clause", &clause_text(&1.member, &1.head, &1.body))
    |> ColumnedList.column(
      "Result",
      &if(&1.compiled == :dead, do: "impossible", else: "compiled")
    )
  end

  defview regions_view(alloc = %Zkfol.Alloc{}, builder) do
    builder.columned_list()
    |> ColumnedList.title("Regions")
    |> ColumnedList.priority(4)
    |> ColumnedList.items(Zkfol.Lay.regions(alloc))
    |> ColumnedList.column("Region", &to_string(&1.name))
    |> ColumnedList.column("Rows", &"#{&1.first}..#{&1.last}")
  end

  defview object_view(rel = %Lang.Rel{}, builder) do
    object_list(rel, builder)
  end

  # A bracket is a row, a bracket of brackets a table; no bracket, nothing drawn.
  @spec object_list(Lang.Rel.t(), module()) :: struct()
  defp object_list(%Lang.Rel{name: name, clauses: clauses}, builder) do
    rows =
      for {head, []} <- clauses,
          bracket <- Enum.filter(head, &Lang.Term.sequence?/1),
          {cells, r} <- bracket |> elements() |> object_rows() |> Enum.with_index(),
          do: {call_text(name, Enum.reject(head, &Lang.Term.sequence?/1)), r, cells}

    object_table(rows, builder)
  end

  @spec object_table([{String.t(), non_neg_integer(), [String.t()]}], module()) :: struct()
  defp object_table([], builder), do: builder.empty()

  defp object_table(rows, builder) do
    list =
      builder.columned_list()
      |> ColumnedList.title("Object")
      |> ColumnedList.priority(3)
      |> ColumnedList.items(rows)
      |> ColumnedList.column("fact", fn {fact, _r, _cells} -> fact end)
      |> ColumnedList.column("r", fn {_fact, r, _cells} -> to_string(r) end)

    width = rows |> Enum.map(fn {_fact, _r, cells} -> length(cells) end) |> Enum.max()

    Enum.reduce(0..(width - 1), list, fn c, list ->
      ColumnedList.column(list, to_string(c), fn {_fact, _r, cells} -> Enum.at(cells, c, "") end)
    end)
  end

  @spec object_rows([Lang.Term.t()]) :: [[String.t()]]
  defp object_rows([]), do: []

  defp object_rows(cells) do
    if Enum.all?(cells, &Lang.Term.sequence?/1),
      do: for(row <- cells, do: for(cell <- elements(row), do: cell_text(cell))),
      else: [for(cell <- cells, do: cell_text(cell))]
  end

  @spec elements(Lang.Term.t()) :: [Lang.Term.t()]
  defp elements({:cons, head, tail}), do: [head | elements(tail)]
  defp elements(nil), do: []

  @spec cell_text(Lang.Term.t()) :: String.t()
  defp cell_text(cell), do: poly_text(cell, &cell_leaf/1)

  @spec cell_leaf(Lang.Term.t()) :: String.t()
  defp cell_leaf({:var, name}) do
    text = to_string(name)
    if String.starts_with?(text, "_"), do: "_", else: text
  end

  defp cell_leaf(cell), do: surface_leaf(cell)

  defview route_view(%Zkfol.Pipeline{passes: passes}, builder) do
    modules = Enum.map(passes, fn {pass, _opts} -> pass end)
    edges = modules |> Enum.zip(Enum.drop(modules, 1)) |> Map.new(fn {a, b} -> {a, [b]} end)

    builder.mondrian()
    |> Mondrian.title("Route")
    |> Mondrian.priority(4)
    |> Mondrian.nodes(modules)
    |> Mondrian.node_label(fn module -> module |> Module.split() |> List.last() end)
    |> Mondrian.edges(fn module -> Map.get(edges, module, []) end)
    |> Mondrian.layout(:tree)
  end

  defview passes_view(%Zkfol.Pipeline{passes: passes}, builder) do
    feed = route(%Zkfol.Pipeline{passes: passes})

    builder.columned_list()
    |> ColumnedList.title("Passes")
    |> ColumnedList.priority(5)
    |> ColumnedList.items(feed.passes)
    |> ColumnedList.column("#", &to_string(&1.index))
    |> ColumnedList.column("Pass", & &1.name)
    |> ColumnedList.column("Options", &(&1.opts || ""))
    |> ColumnedList.column("Implements", &Enum.join(&1.implements, ", "))
    |> ColumnedList.column("Says", &(&1.says || ""))
    |> ColumnedList.send(& &1.module)
  end

  @spec mode_feed(Uair.mode()) :: [map()]
  defp mode_feed(%Uair.Composed{reads: reads}), do: reads
  defp mode_feed(_plain), do: []

  @spec kinds([pos_integer() | :x | :ones], [map()], [tuple()], [tuple()]) :: [atom()]
  defp kinds(rows, reads, shifts, limbs) do
    bit = reads |> Enum.flat_map(& &1.bit_rows) |> MapSet.new()
    result = MapSet.new(reads, & &1.result_row)
    pointer = MapSet.new(reads, & &1.row)
    scheduled = MapSet.new(shifts, &elem(&1, 0))
    ranged = MapSet.new(limbs, &elem(&1, 0))
    index = Enum.find_index(rows, &(&1 == :x))

    for i <- 0..(length(rows) - 1) do
      cond do
        i in bit -> :bit
        i in result -> :result
        i in pointer -> :pointer
        i in ranged -> :ranged
        i in scheduled -> :scheduled
        i == index -> :index
        true -> :plain
      end
    end
  end

  @spec first_sentence(module()) :: String.t() | nil
  defp first_sentence(mod) do
    with {:docs_v1, _anno, _lang, _fmt, %{"en" => doc}, _meta, _docs} <- Code.fetch_docs(mod) do
      doc |> String.replace("\n", " ") |> String.split(~r/(?<=\.)\s/, parts: 2) |> hd()
    else
      _absent -> nil
    end
  end

  # Reify is the term its predicate already is, so it shows nothing of its own.
  @spec tree(Ast.pred() | Ast.term_t(), Interpretation.t(), pos_integer()) ::
          %{atom() => term()}
  defp tree({:reify, phi}, w, x), do: tree(phi, w, x)

  defp tree(node, w, x) do
    children =
      for {child, role} <- shown(node) do
        subtree = tree(child, w, x)
        if role, do: Map.put(subtree, :role, role), else: subtree
      end

    drawn = %{text: said(node), value: Semantics.eval(node, w, x), children: children}

    case Ast.read(node) do
      {_i, address} -> Map.put(drawn, :at, Semantics.column(address, w, x))
      nil -> drawn
    end
  end

  @spec said(Ast.pred() | Ast.term_t()) :: String.t()
  defp said(node)
       when is_tuple(node) and
              elem(node, 0) in [:eq, :conj, :disj, :natural, :permutes, :distinct, :permuted],
       do: phi_text(node)

  defp said(node), do: term_text(node)

  @spec shown(Ast.pred() | Ast.term_t()) :: [{Ast.pred() | Ast.term_t(), String.t() | nil}]
  defp shown({:eq, t, u}), do: [{t, "left"}, {u, "right"}]
  defp shown({:natural, t}), do: [{t, "left"}]

  defp shown({tag, t, u}) when tag in [:add, :mul],
    do: for(part <- [t, u], not is_integer(part), do: {part, nil})

  defp shown(node) do
    case Ast.read(node) do
      {_i, {:at, {:cell, j}, _mul, _add}} -> [{Ast.cell(j), "pointer"}]
      {_i, _address} -> []
      nil -> for(child <- Ast.children(node), do: {child, nil})
    end
  end

  @spec sources(Statement.t(), non_neg_integer()) :: [String.t()]
  defp sources(statement, n) do
    written =
      for %Lang.Rel{name: name, clauses: clauses} <- ordered(statement),
          text <- ["" | for({head, body} <- clauses, do: clause_text(name, head, body))],
          do: text

    if length(written) == n, do: written, else: []
  end

  @spec clause_text(atom(), [term()], [term()]) :: String.t()
  def clause_text(name, head, []), do: call_text(name, head)

  def clause_text(name, head, body),
    do: call_text(name, head) <> " do " <> Enum.map_join(body, "; ", &goal_text/1) <> " end"

  @spec call_text(Zkfol.Lang.Term.name(), [term()]) :: String.t()
  defp call_text({mod, name}, args), do: call_text(:"#{inspect(mod)}.#{name}", args)
  defp call_text(name, args), do: "#{name}(#{Enum.map_join(args, ", ", &surface_text/1)})"

  @spec goal_text(term()) :: String.t()
  defp goal_text({:call, {:var, name}, args}), do: call_text(name, args)
  defp goal_text({:call, name, args}), do: call_text(name, args)
  defp goal_text({:eq, t, u}), do: surface_text(t) <> " = " <> surface_text(u)

  @spec surface_text(term()) :: String.t()
  def surface_text(term), do: poly_text(term, &surface_leaf/1)

  @spec surface_leaf(term()) :: String.t()
  defp surface_leaf({:var, name}), do: to_string(name)
  defp surface_leaf({:papply, name, []}), do: call_text(name, [])
  defp surface_leaf({:papply, name, args}), do: call_text(name, args)
  defp surface_leaf({:reify, goal}), do: "reify(" <> goal_text(goal) <> ")"
  defp surface_leaf(_pinned), do: "^"

  @spec conjuncts_of(Ast.pred()) :: [Ast.pred()]
  defp conjuncts_of({:conj, goals}), do: goals
  defp conjuncts_of(pred), do: [pred]

  @spec phi_text(Ast.pred()) :: String.t()
  def phi_text({:eq, t, u}), do: term_text(t) <> " = " <> term_text(u)
  def phi_text({:natural, t}), do: "natural(" <> term_text(t) <> ")"
  def phi_text({:conj, goals}), do: Enum.map_join(goals, " and ", &phi_text/1)
  def phi_text({:disj, goals}), do: Enum.map_join(goals, " or ", &phi_text/1)

  def phi_text({:permutes, cells, values}),
    do:
      "permutes(" <>
        Enum.map_join(cells, ", ", &term_text/1) <>
        " : #{List.first(values)}..#{List.last(values)})"

  def phi_text({:distinct, cells}),
    do: "distinct(" <> Enum.map_join(cells, ", ", &term_text/1) <> ")"

  def phi_text({:permuted, cells, copy}),
    do:
      "permuted(" <>
        Enum.map_join(cells, ", ", &term_text/1) <>
        " ~ " <> Enum.map_join(copy, ", ", &term_text/1) <> ")"

  @spec term_text(Ast.term_t()) :: String.t()
  defp term_text(term), do: poly_text(term, &ast_leaf/1)

  @spec ast_leaf(Ast.term_t()) :: String.t()
  defp ast_leaf(:x), do: "X"
  defp ast_leaf({:cell, _i} = read), do: read_text(read)
  defp ast_leaf({:cell, _i, _address} = read), do: read_text(read)
  defp ast_leaf({:reify, phi}), do: "[" <> phi_text(phi) <> "]"

  @spec read_text(Ast.term_t()) :: String.t()
  defp read_text(read) do
    {i, address} = Ast.read(read)
    "#{ref_text(i)}(#{term_text(Ast.naming(address))})"
  end

  @spec ref_text(Ast.row_ref()) :: String.t()
  defp ref_text(ref = {_sym, _i}), do: row_text(ref)
  defp ref_text(i), do: "C#{i}"

  # Ast's terms and the surface's share the sum-and-product spine; the leaf renderer
  # is the whole of the difference, parenthesisation included.
  @spec poly_text(term(), (term() -> String.t())) :: String.t()
  defp poly_text(q, _leaf) when is_integer(q), do: Integer.to_string(q)
  defp poly_text(:len, _leaf), do: "len"

  defp poly_text({:add, t, q}, leaf) when is_integer(q) and q < 0,
    do: poly_text(t, leaf) <> " - " <> Integer.to_string(-q)

  defp poly_text({:add, t, u}, leaf), do: poly_text(t, leaf) <> " + " <> poly_text(u, leaf)
  defp poly_text({:mul, t, u}, leaf), do: factor(t, leaf) <> "*" <> factor(u, leaf)
  defp poly_text(term, leaf), do: leaf.(term)

  @spec factor(term(), (term() -> String.t())) :: String.t()
  defp factor({:add, _t, _u} = t, leaf), do: "(" <> poly_text(t, leaf) <> ")"
  defp factor(t, leaf), do: poly_text(t, leaf)

  @spec labels(Statement.t(), non_neg_integer()) :: [String.t()]
  defp labels(statement, n) do
    named =
      for %Lang.Rel{name: name, clauses: clauses} <- ordered(statement),
          text <- [
            "no #{name}"
            | for {head, body} <- clauses do
                case body do
                  [] -> "#{name}(#{head |> Enum.map(&surface_text/1) |> Enum.join(",")})"
                  _rule -> "#{name} rule"
                end
              end
          ],
          do: text

    if length(named) == n, do: named, else: for(i <- 1..n//1, do: "branch #{i}")
  end

  @spec ordered(Statement.t()) :: [Lang.Rel.t()]
  defp ordered(%Statement{rels: rels, stage: %Solved{lay: lay}}) do
    named = Map.new(rels, &{&1.name, &1})

    for %Zkfol.Alloc.Member{relation: relation} <- lay.alloc.members,
        rel = named[relation],
        do: rel
  end

  @spec inspected(term()) :: String.t()
  def inspected(term), do: inspect(term, pretty: true, limit: 100, printable_limit: 2048)
end
