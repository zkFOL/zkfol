defmodule Zkfol.Alloc do
  @moduledoc """
  I am the layout: the members a statement's relations stand on, the banks their sequences
  fill, and the row every reference names in the one committed matrix.

  ### Public API

  - `refs/1`, `slot_rows/2`, `defaults/1`: every assigned row, and its padding value.
  - `row/2`, `rows/2`, `regions/1`, `width/1`: where a reference, a symbol, every symbol, all
    of it lands.
  - `presence/2`: the row a member's facts stand on.
  - `numbered/2`, `root/1`, `member/2`, `names/1`: the members a walk made, the root, one by
    name, their names.
  - `link/2`, `aimed/2`: named references to absolute rows.
  """

  use TypedStruct

  alias Zkfol.Ast

  @typedoc """
  Where a parameter stands relative to its member's column.

      {:cell, ref}            a scalar on my member’s column
      {:bank, name, address}   a sequence in the named bank, its head at the address
      {:column, origin}        the column itself, X + origin; no row
      {:node, ref}             a term identity on a row at my member’s column
      {:rel, name, rows}       a relation passed by name, its fixed arguments on these rows
      :none                    no row of the trace: a value standing elsewhere
  """
  @type allocation ::
          {:cell, Ast.row_ref()}
          | {:rel, atom(), [Ast.row_ref()]}
          | {:bank, atom(), Ast.address()}
          | {:column, integer()}
          | {:node, Ast.row_ref()}
          | :none

  defmodule Source do
    @moduledoc """
    I locate a witness value independently of its storage. `calls` follows source calls
    from the member's fact; `binding` selects an argument or a clause variable. A local
    belongs to one member clause; `nil` reads an argument in every clause.
    """
    use TypedStruct

    typedstruct do
      field(:calls, [{atom(), non_neg_integer()}], default: [])
      field(:binding, {:argument, non_neg_integer()} | {:variable, atom()}, enforce: true)
      field(:clause, non_neg_integer() | nil)
    end
  end

  defmodule Slot do
    @moduledoc "I pair a value's source with its storage; address slots are filled by calls."
    use TypedStruct

    typedstruct enforce: true do
      field(:name, Zkfol.Phi.Expression.name())
      field(:allocation, Zkfol.Alloc.allocation())
      field(:source, Zkfol.Alloc.Source.t() | nil, default: nil)
    end
  end

  defmodule Bank do
    @moduledoc "I am rows a sequence's cells stand on: `depth` of them, one element a column."
    use TypedStruct

    typedstruct enforce: true do
      field(:name, atom())
      field(:depth, pos_integer())
      field(:element, Zkfol.Phi.Shape.t(), default: :unknown)
    end

    @doc "I am the name of the bank a parameter's cells stand in."
    @spec of(Zkfol.Ast.row_ref()) :: atom()
    def of({name, {:param, sym}}) do
      :"#{name} #{sym}"
    end

    @doc "I am the rows of the bank `name`, `depth` deep."
    @spec rows(atom(), pos_integer()) :: [Zkfol.Ast.row_ref()]
    def rows(name, depth) do
      Enum.map(1..depth//1, &{name, &1})
    end
  end

  defmodule Site do
    @moduledoc """
    I am a source call and where its callee stands. `source` follows the calls through
    inlined clauses: each relation and its occurrence among calls to that relation.
    The address is affine in the caller's column or reads a pointer cell.
    """
    use TypedStruct

    typedstruct enforce: true do
      field(:callee, atom())
      field(:address, Zkfol.Ast.address())
      field(:source, [{atom(), non_neg_integer()}])
    end
  end

  defmodule Member do
    @moduledoc """
    I am one relation as a call site reaches it, `relation` its name in the surface: a slot
    per parameter and per row a phi spent, and the sites each clause of mine calls through,
    by clause index. `steps` is the parameter my column counts and the count my first column
    stands for, none where I count nothing.
    """
    use TypedStruct

    typedstruct enforce: true do
      field(:name, atom())
      field(:relation, atom())
      field(:slots, [Zkfol.Alloc.Slot.t()])
      field(:steps, {non_neg_integer(), integer()} | nil)
      field(:sites, %{non_neg_integer() => [Zkfol.Alloc.Site.t()]})
    end
  end

  typedstruct enforce: true do
    field(:members, [Member.t() | Bank.t() | Zkfol.Nodes.t()])
  end

  @doc "I am every row I assign, in order: each member's own rows, then one presence row a member."
  @spec refs(t()) :: [Ast.row_ref()]
  def refs(%__MODULE__{members: members}) do
    Enum.flat_map(members, &spent/1) ++
      for(member <- members, not is_struct(member, Zkfol.Nodes), do: {:in, member.name})
  end

  @doc "I am the symbolic rows a slot uses; a bank owns its dimensions."
  @spec slot_rows(t(), Slot.t()) :: [Ast.row_ref()]
  def slot_rows(alloc, %Slot{allocation: {:bank, name, _address}}) do
    %Bank{depth: depth} = member(alloc, name)
    Bank.rows(name, depth)
  end

  def slot_rows(_alloc, %Slot{allocation: {kind, ref}}) when kind in [:cell, :node], do: [ref]
  def slot_rows(_alloc, %Slot{}), do: []

  @doc "I give pointer and term identities a valid padding value; other rows pad zero."
  @spec defaults(t()) :: %{pos_integer() => 1}
  def defaults(alloc = %__MODULE__{members: members}) do
    refs =
      Enum.flat_map(members, fn
        %Member{slots: slots, sites: sites} ->
          nodes = for %Slot{allocation: {:node, ref}} <- slots, do: ref

          pointers =
            for calls <- Map.values(sites),
                %Site{address: {:at, {:cell, ref}, _m, _a}} <- calls,
                do: ref

          nodes ++ pointers

        %Zkfol.Nodes{refs: refs} ->
          for {Zkfol.Nodes, field} = ref <- refs, field not in [:tag, :value], do: ref

        %Bank{} ->
          []
      end)

    Map.new(refs, &{row(alloc, &1), 1})
  end

  @doc "I am the absolute row a reference names."
  @spec row(t(), Ast.row_ref()) :: pos_integer()
  def row(_alloc, i) when is_integer(i) do
    i
  end

  def row(alloc = %__MODULE__{}, ref) do
    Enum.find_index(refs(alloc), &(&1 == ref)) + 1
  end

  @doc "I am the rows of `sym`: absolute, 1-based, in region order, none where I hold no `sym`."
  @spec rows(t(), atom()) :: Range.t() | nil
  def rows(alloc = %__MODULE__{}, sym) do
    case for({{^sym, _which}, i} <- Enum.with_index(refs(alloc), 1), do: i) do
      [] -> nil
      at -> hd(at)..List.last(at)//1
    end
  end

  @doc "I am the rows each symbol takes, in order, the presence rows last."
  @spec regions(t()) :: [{atom(), pos_integer()}]
  def regions(alloc = %__MODULE__{}) do
    Enum.map(Enum.chunk_by(refs(alloc), &elem(&1, 0)), &{elem(hd(&1), 0), length(&1)})
  end

  @doc "I am how many rows I assign in all."
  @spec width(t()) :: non_neg_integer()
  def width(alloc = %__MODULE__{}) do
    length(refs(alloc))
  end

  @doc "I am the absolute row the facts of `name` stand on."
  @spec presence(t(), atom()) :: pos_integer()
  def presence(alloc = %__MODULE__{}, name) do
    row(alloc, {:in, name})
  end

  @doc "I am the members a walk made, in rows, the root first."
  @spec numbered([Member.t() | Bank.t() | Zkfol.Nodes.t()], atom()) :: t()
  def numbered(made, root) do
    %__MODULE__{members: Enum.sort_by(made, &(&1.name != root))}
  end

  @doc "I am the root member: the relation the act named, first among my members."
  @spec root(t()) :: Member.t()
  def root(%__MODULE__{members: [root | _rest]}) do
    root
  end

  @doc "I am the member or bank named `name`."
  @spec member(t(), atom()) :: Member.t() | Bank.t() | Zkfol.Nodes.t() | nil
  def member(%__MODULE__{members: members}, name) do
    Enum.find(members, &(&1.name == name))
  end

  @doc "I am my members' names, in order."
  @spec names(t() | [Member.t() | Bank.t() | Zkfol.Nodes.t()]) :: [atom()]
  def names(%__MODULE__{members: members}) do
    names(members)
  end

  def names(members) when is_list(members) do
    Enum.map(members, & &1.name)
  end

  @doc "I am the absolute row a pointer address reads, none where it is affine in the column."
  @spec aimed(t(), Ast.address()) :: pos_integer() | nil
  def aimed(alloc = %__MODULE__{}, {:at, {:cell, ref}, _mul, _add}) do
    row(alloc, ref)
  end

  def aimed(%__MODULE__{}, {:at, :x, _mul, _add}) do
    nil
  end

  @doc "I resolve every named reference to its absolute row; numeric ones pass through."
  @spec link(Ast.pred(), t()) :: Ast.pred()
  def link(pred, alloc = %__MODULE__{}) do
    Ast.postwalk(pred, &resolve(&1, alloc))
  end

  ############################################################
  #                   Private Implementation                 #
  ############################################################

  @spec spent(Member.t() | Bank.t() | Zkfol.Nodes.t()) :: [Ast.row_ref()]
  defp spent(%Zkfol.Nodes{refs: refs}), do: refs

  defp spent(%Bank{name: name, depth: depth}) do
    Bank.rows(name, depth)
  end

  defp spent(%Member{slots: slots}) do
    Enum.flat_map(slots, fn
      %Slot{allocation: {kind, ref}} when kind in [:cell, :node] -> [ref]
      %Slot{allocation: {:rel, _name, rows}} -> rows
      _slot -> []
    end)
  end

  @spec resolve(term(), t()) :: term()
  defp resolve({:cell, _ref} = read, alloc) do
    linked(read, alloc)
  end

  defp resolve({:cell, _ref, _address} = read, alloc) do
    linked(read, alloc)
  end

  defp resolve(node, _alloc) do
    node
  end

  @spec linked(Ast.term_t(), t()) :: Ast.term_t()
  defp linked(read, alloc) do
    {ref, {:at, _base, mul, add} = address} = Ast.read(read)
    ptr = aimed(alloc, address)
    Ast.at(row(alloc, ref), (ptr && {:cell, ptr}) || :x, mul, add)
  end
end
