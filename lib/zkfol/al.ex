defmodule Zkfol.Al do
  @moduledoc """
  I translate FOL clauses to AL methods, install them, and call them with query arguments.
  Clause bodies run in source order. Terms map directly to AL terms;
  passed relations are AL compounds carrying their captured arguments.
  `len` becomes an AL variable; clauses constrain it with ordinary equations.

  ### Public API

  - `install/3`, `invoke/3`, `close/1`: install clauses, call a method, release its methods.
  - `result/1`: interpret an AL transaction result.
  - `derived/3`: run with AL tracing and return the derivation used by the prover.
  - `method/1`: map a relation name to its AL method name.
  """

  alias Zkfol.{Ast, Derivation, Log, Program, Refusal, Statement}
  alias Zkfol.Lang.{Rel, Term}

  @self AL.Var.var("_Self")
  @object AL.Var.var("_Object")
  @heap 256_000_000

  @type target :: Statement.t() | Rel.t() | [Rel.t()]
  @type result :: {:ok, AL.JAM.State.t()} | {:no, term()} | {:error, Refusal.t()}

  @doc "I install the translated clauses and return their object and prepared statement."
  @spec install(target(), [Statement.datum() | :_], keyword()) ::
          {:ok, AL.Object.t(), Statement.t()} | {:error, Refusal.t()}
  def install(target, arguments, opts), do: install(target, arguments, opts, false)

  defp install(target, arguments, opts, trace?) do
    with {:ok, [root | _] = rels} <- relations(target),
         {:ok, arguments} <- pad(arguments, root.arity),
         clauses = for(rel <- rels, clause <- rel.clauses, do: clause(rel, clause, trace?)),
         branch = branch(Keyword.get(opts, :branch)),
         {:ok, state} <- run([call(:new, [:object, @object]) | clauses], branch) do
      program = %AL.Object{
        id: AL.Var.subst(@object, state.active_choicepoint.store),
        branch: branch.id
      }

      {:ok, program, %Statement{rels: rels, args: arguments}}
    else
      {:no, reason} -> {:error, {:send_failed, %{reason: reason}}}
      {:error, _} = refusal -> refusal
    end
  catch
    {:refused, reason} -> {:error, reason}
  end

  @doc "I call the installed root with the prepared statement's arguments and optional AL tracing."
  @spec invoke(AL.Object.t(), Statement.t(), keyword()) :: result()
  def invoke(program, %Statement{rels: [root | _], args: arguments}, opts \\ []) do
    args = Enum.map(arguments, &query_argument/1)

    run(
      [call(method(root.name), [program.id | args ++ [fresh()]])],
      branch(program.branch),
      opts
    )
  end

  @doc "I distinguish an AL answer, exhausted search, and a resource refusal."
  @spec result(term()) :: result()
  def result(%AL{result: result}), do: result(result)
  def result({:atomic, {_bindings, _constraints, state}}), do: {:ok, state}

  def result({:aborted, %{reason: {:resource_limit_exceeded, n}}}),
    do: {:error, {:unresolved_within_budget, %{reductions: n}}}

  def result({:aborted, reason}), do: {:no, reason}
  def result(error), do: Refusal.from_al(error)

  @doc "I run the installed program with tracing and return its first derivation."
  @spec derived(target(), [Statement.datum() | :_], keyword()) ::
          {:ok, Derivation.t()} | {:error, Refusal.t()}
  def derived(target, arguments, opts \\ []) do
    with {:ok, program, source} <- install(target, arguments, opts, true) do
      name = Keyword.get(opts, :name, hd(source.rels).name)

      with {:ok, derivation} <- derive(program, source, Keyword.get(opts, :heap) || @heap) do
        Log.push(
          {:al_solved, %{name: name, count: length(derivation.facts), program: program}},
          Keyword.get(opts, :basedon)
        )

        {:ok, derivation}
      else
        {:no, _} -> {:error, {:no_answer, %{relation: name}}}
        {:error, _} = refusal -> refusal
      end
    end
  end

  @doc "I retract this program's methods, leaving other installed programs intact."
  @spec close(AL.Object.t()) :: :ok | {:error, Refusal.t()}
  def close(program = %AL.Object{}) do
    name = fresh()
    implementation = fresh()

    goals = [
      call(:forall, [
        call(:method, [program.id, name, implementation]),
        call(:vm_retract_method, [program.id, name, implementation])
      ])
    ]

    with {:ok, _} <- run(goals, branch(program.branch)), do: :ok
  end

  @doc "I prefix relation names so they cannot shadow native AL methods such as `concat`."
  @spec method(Term.name()) :: atom()
  def method(name), do: :"rel:#{Rel.name(name)}"

  defp clause(%Rel{al: {:definition, native}} = rel, {head, body}, trace?),
    do: clause(%{rel | al: native}, {head, if(trace?, do: body, else: [])}, trace?)

  defp clause(rel, {head, body}, trace?) do
    for term <- head,
        not Term.seatable?(term),
        do: throw({:refused, {:head_not_a_column, %{head: term}}})

    # Source locals must survive the call so the derivation can bind proof columns.
    locals = if trace?, do: Map.new(Term.names(head ++ body), &{&1, var(&1)}), else: %{}

    call(:defmethod, [
      @object,
      method(rel.name),
      [@self | Enum.map(head, &term/1) ++ [locals]],
      native(rel.al) ++ Enum.flat_map(body, &goal/1)
    ])
  end

  defp goal({:eq, left, right}), do: [call(:=, [term(left), term(right)])]

  defp goal({:call, name, args}), do: dispatch(name, Enum.map(args, &term/1) ++ [fresh()])

  defp dispatch({:var, carrier}, args) do
    [name, prefix, supplied] = for _ <- 1..3, do: fresh()

    [
      call(:functor, [var(carrier), name, prefix]),
      call(:concat, [prefix, args, supplied]),
      call(:send, [@self, name, supplied])
    ]
  end

  defp dispatch(name, args), do: [call(method(name), [@self | args])]

  defp term(n) when is_integer(n), do: n
  defp term(nil), do: []
  defp term(:len), do: var(:len)
  defp term({:var, name}), do: var(name)
  defp term({:reify, {:eq, left, right}}), do: term(Ast.arithmetize(Ast.eq(left, right)))

  defp term({op, left, right}) when op in [:add, :mul],
    do: call(if(op == :add, do: :+, else: :*), [term(left), term(right)])

  defp term({:cons, head, tail}), do: [term(head) | term(tail)]
  defp term({:papply, name, prefix}), do: call(method(name), Enum.map(prefix, &term/1))

  defp term(term), do: throw({:refused, {:unliftable_term, %{term: term}}})

  defp native(nil), do: []

  defp native(text) do
    {:ok, %AL.Syntax.Result{program: goals}} = AL.Syntax.parse(text <> ".")
    goals
  end

  defp run(goals, branch, opts \\ []),
    do: goals |> AL.eval(nil, branch, opts) |> AL.post_commit() |> result()

  # Only the derivation leaves the capped process, not AL's search state.
  defp derive(program, source, heap) do
    {pid, ref} =
      spawn_monitor(fn ->
        Process.flag(:max_heap_size, %{size: heap, kill: true, error_logger: false})
        names = Map.new(source.rels, &{method(&1.name), {&1.name, &1.arity}})

        result =
          with {:ok, state} <- invoke(program, source, trace: [:domino]),
               do: {:ok, Derivation.of(state, names)}

        exit({:derived, result})
      end)

    receive do
      {:DOWN, ^ref, :process, ^pid, {:derived, result}} ->
        result

      {:DOWN, ^ref, :process, ^pid, _} ->
        {:error, {:heap_exhausted, %{said: "the derivation exceeded #{heap} heap words"}}}
    end
  end

  defp relations(%Statement{rels: rels}), do: relations(rels)
  defp relations(root = %Rel{}), do: relations([root])
  defp relations([root | _] = rels), do: Program.reached(root, rels)
  defp relations([]), do: {:error, {:no_relations, %{}}}

  defp pad(args, arity) when length(args) > arity,
    do: {:error, {:arguments_exceed_rows, %{args: length(args), rows: arity}}}

  defp pad(args, arity), do: {:ok, args ++ List.duplicate(:_, arity - length(args))}

  defp query_argument(:_), do: fresh()
  defp query_argument(name) when is_atom(name), do: var(name)
  defp query_argument(value), do: value

  defp branch(id) when id in [nil, :head], do: AL.Branch.head()
  defp branch(id), do: %AL.Branch{id: id}
  defp var(name), do: name |> Atom.to_string() |> :string.titlecase() |> AL.Var.var()
  defp fresh, do: AL.Var.fresh(AL.Var.var("_Tmp"), to_string(AL.fresh_scope()))
  defp call(name, args), do: %AL.Goal.Compound{name: name, args: args}
end
