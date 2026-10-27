defmodule Zkfol.Doubling do
  @moduledoc """
  I am the doubling rewrite: an order-2 recurrence's length-n index ladder becomes a walk
  over the bits of the position, on the kernel pair U (U(1) = 1, U(2) = p):

      U(2e)   = U(e) · (2·U(e+1) − p·U(e))
      U(2e+1) = q·U(e)² + U(e+1)²
      x(n)    = x₂·U(m−1) + q·x₁·U(m−2)    at position m = n − start + 1
  """

  @behaviour Zkfol.Pipeline

  import Zkfol.Prims, only: [mod: 0]

  alias Zkfol.Al
  alias Zkfol.Facts
  require Zkfol.Lang
  alias Zkfol.Lang.Rel
  alias Zkfol.Refusal
  alias Zkfol.Statement

  @doc "I am the rewrite as a pass, always a try: an uncertified statement passes through."
  @impl Zkfol.Pipeline
  @spec run(Statement.t(), keyword()) :: {:ok, Statement.t()} | {:error, Refusal.t()}
  def run(statement = %Statement{rels: [root | _rest], args: [n | args]}, opts)
      when is_integer(n) and length(args) <= 1 do
    with {:ok, [root = %Rel{al: nil, phi: nil} | helpers]} <-
           Zkfol.Program.reached(root, statement.rels),
         {:ok, descriptor} <- Facts.of(root),
         {:ok, [_root | ^helpers]} <- Zkfol.Program.reached(root, [root]),
         true <- descriptor.modulus == nil or natural?(descriptor.coefficients) do
      rewritten(descriptor, n, List.first(args, :_), named(statement, opts))
    else
      _uncertified -> {:ok, statement}
    end
  end

  def run(statement, _opts), do: {:ok, statement}

  @impl Zkfol.Pipeline
  @spec verb() :: Zkfol.Pipeline.result()
  def verb, do: :rewrites

  # A reduced step commits every value as a natural, so its coefficients must be.
  @spec natural?({integer(), integer()}) :: boolean()
  defp natural?({p, q}), do: p >= 0 and q >= 0

  @spec rewritten(Facts.t(), integer(), Statement.datum() | :_, keyword()) ::
          {:ok, Statement.t()} | {:error, Refusal.t()}
  defp rewritten(descriptor = %Facts{base: [{start, x1}, {_, x2}]}, n, result, opts) do
    case n - start + 1 do
      m when m < 1 ->
        {:error, {:precedes_base_case, %{n: n, base: start}}}

      1 ->
        trivial(x1, result, opts)

      2 ->
        trivial(x2, result, opts)

      m ->
        build(descriptor, m, result, Keyword.take(opts, [:branch, :heap, :name, :basedon]))
    end
  end

  # One new atom per relation, bounded by the program.
  defp named(%Statement{rels: [root | _rest]}, opts),
    do: Keyword.put_new(opts, :name, :"#{root.name}_kernel")

  defp named(_statement, opts), do: opts

  @spec trivial(integer(), Statement.datum() | :_, keyword()) ::
          {:ok, Statement.t()} | {:error, Refusal.t()}
  defp trivial(value, result, opts) do
    one =
      Zkfol.Lang.rel do
        one(1, ^value)
      end

    with {:ok, solved} <-
           solved(one, [1, result], Keyword.take(opts, [:branch, :heap, :basedon])),
         do: {:ok, %Statement{rels: [one], stage: solved}}
  end

  @spec build(Facts.t(), pos_integer(), Statement.datum() | :_, keyword()) ::
          {:ok, Statement.t()} | {:error, Refusal.t()}
  defp build(descriptor, m, result, solve_opts) do
    statement = %Statement{rels: [kernel(descriptor)]}
    derived(statement, m, result, solve_opts)
  end

  @spec derived(Statement.t(), pos_integer(), Statement.datum() | :_, keyword()) ::
          {:ok, Statement.t()} | {:error, Refusal.t()}
  defp derived(statement = %Statement{rels: rels}, m, result, solve_opts) do
    with {:ok, solved} <- solved(rels, [count(m), :_, :_, m - 2, result], solve_opts),
         do: {:ok, %{statement | stage: solved}}
  end

  # A statement derived and laid: the two passes the rewrite runs on what it builds.
  @spec solved([Rel.t()] | Rel.t(), [Statement.datum() | :_], keyword()) ::
          {:ok, Statement.Solved.t()} | {:error, Refusal.t()}
  defp solved(rels, arguments, opts) do
    statement = Statement.of(rels)

    with {:ok, derivation} <- Al.derived(statement, arguments, opts),
         {:ok, laid} <- Zkfol.Phi.relaid(statement, derivation),
         do: {:ok, laid.stage}
  end

  @spec base(Facts.t()) :: [integer()]
  defp base(%Facts{coefficients: {p, q}, base: [{_, x1}, {_, x2}], modulus: mod}),
    do: [1, rem(1, mod), rem(p, mod), 1, rem(x2 * p + q * x1, mod)]

  @spec count(pos_integer()) :: pos_integer()
  defp count(m), do: (m - 2) |> Integer.digits(2) |> length()

  @spec kernel(Facts.t()) :: Rel.t()
  defp kernel(%Facts{coefficients: {p, q}, base: [{_, x1}, {_, x2}], modulus: nil}) do
    Zkfol.Lang.rel do
      kernel(1, 1, ^p, 1, ^(x2 * p + q * x1))

      kernel(x, u, w, e, r) do
        x > 1
        e = 2 * ee + 0
        r = ^x2 * w + ^(q * x1) * u
        x1 = x - 1
        kernel(x1, uu, ww, ee, _rr)
        u = uu * (2 * ww + ^(-p) * uu)
        w = ^q * (uu * uu) + ww * ww
      end

      kernel(x, u, w, e, r) do
        x > 1
        e = 2 * ee + 1
        r = ^x2 * w + ^(q * x1) * u
        x1 = x - 1
        kernel(x1, uu, ww, ee, _rr)
        u = ^q * (uu * uu) + ww * ww
        w = ^p * u + ^q * (uu * (2 * ww + ^(-p) * uu))
      end
    end
  end

  # `p * mod` rides the subtraction so every committed value is a natural.
  defp kernel(descriptor = %Facts{coefficients: {p, q}, base: [{_, x1}, {_, x2}], modulus: mod}) do
    [_x, u0, w0, _e, r0] = base(descriptor)

    Zkfol.Lang.rel do
      kernel(1, ^u0, ^w0, 1, ^r0)

      kernel(x, u, w, e, r) do
        x > 1
        e = 2 * ee + 0
        x1 = x - 1
        kernel(x1, uu, ww, ee, _rr)
        mod(uu * (2 * ww + ^(p * mod) + ^(-p) * uu), ^mod, u)
        mod(^q * (uu * uu) + ww * ww, ^mod, w)
        mod(^x2 * w + ^(q * x1) * u, ^mod, r)
      end

      kernel(x, u, w, e, r) do
        x > 1
        e = 2 * ee + 1
        x1 = x - 1
        kernel(x1, uu, ww, ee, _rr)
        mod(^q * (uu * uu) + ww * ww, ^mod, u)
        mod(^p * u + ^q * (uu * (2 * ww + ^(p * mod) + ^(-p) * uu)), ^mod, w)
        mod(^x2 * w + ^(q * x1) * u, ^mod, r)
      end
    end
  end
end
