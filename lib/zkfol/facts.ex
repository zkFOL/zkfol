defmodule Zkfol.Facts do
  @moduledoc """
  I am an order-2 linear recurrence read off a relation's clauses:

      f(a, x1)   f(a + 1, x2)
      f(n, v) :- n > a + 1, f(n - 1, u), f(n - 2, w), v = p * u + q * w

  The definition of `v` may reduce, `v = mod(p * u + q * w, m)`; the guard may be absent.
  """

  use TypedStruct

  alias Zkfol.Lang.Rel
  alias Zkfol.Prims
  alias Zkfol.Refusal

  typedstruct enforce: true do
    field(:base, [{pos_integer(), integer()}])
    field(:coefficients, {integer(), integer()})
    field(:modulus, pos_integer() | nil)
  end

  @doc "I read the recurrence `rel` is, or refuse."
  @spec of(Rel.t()) :: {:ok, t()} | {:error, Refusal.t()}
  def of(%Rel{
        name: f,
        clauses: [{[a, x1], []}, {[b, x2], []}, {[{:var, n}, {:var, v}], body}]
      })
      when is_integer(a) and is_integer(x1) and is_integer(x2) and b == a + 1 do
    {guards, goals} = Enum.split_with(body, &guard?(&1, n))

    with true <- Enum.all?(guards, &above?(&1, b)),
         [
           {:call, f1, [{:add, {:var, ^n}, -1}, {:var, u}]},
           {:call, f2, [{:add, {:var, ^n}, -2}, {:var, w}]},
           definition
         ] <- Enum.sort_by(goals, &elem(&1, 0)),
         true <- Rel.name(f1) == f and Rel.name(f2) == f,
         {rhs, modulus} <- defined(definition, v),
         %{^u => p, ^w => q} = combination when map_size(combination) == 2 <- linear(rhs),
         4 <- length(Enum.uniq([n, v, u, w])) do
      {:ok, %__MODULE__{base: [{a, x1}, {b, x2}], coefficients: {p, q}, modulus: modulus}}
    else
      _other -> {:error, {:not_a_recurrence, %{relation: f}}}
    end
  end

  def of(%Rel{name: f}), do: {:error, {:not_a_recurrence, %{relation: f}}}

  @spec guard?(term(), atom()) :: boolean()
  defp guard?({:call, op, [{:var, n}, _bound, _slack]}, n), do: op in [&Prims.gt/0, &Prims.gte/0]
  defp guard?(_goal, _n), do: false

  # The step applies exactly above the base, spelled either way.
  @spec above?(term(), integer()) :: boolean()
  defp above?({:call, op, [_n, bound, _slack]}, last),
    do: bound == last + if(op == (&Prims.gte/0), do: 1, else: 0)

  @spec defined(term(), atom()) :: {term(), pos_integer() | nil} | nil
  defp defined({:eq, {:var, v}, rhs}, v), do: {rhs, nil}

  defp defined({:call, op, [rhs, m, {:var, v}, {:var, _q}]}, v) when is_integer(m) and m > 0,
    do: if(op == (&Prims.mod/0), do: {rhs, m})

  defp defined(_goal, _v), do: nil

  # The coefficient of each name in a linear combination; nil where a term is not one.
  @spec linear(term()) :: %{atom() => integer()} | nil
  defp linear({:var, u}), do: %{u => 1}
  defp linear({:mul, {:var, u}, c}) when is_integer(c), do: %{u => c}
  defp linear({:mul, c, {:var, u}}) when is_integer(c), do: %{u => c}

  defp linear({:add, s, t}) do
    with %{} = a <- linear(s), %{} = b <- linear(t), do: Map.merge(a, b, fn _u, x, y -> x + y end)
  end

  defp linear(_term), do: nil
end
