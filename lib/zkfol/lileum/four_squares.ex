defmodule Zkfol.Lileum.FourSquares do
  @moduledoc "I construct the four-square witnesses used by Lileum's naturality constraints."

  @doc "I return four nonnegative integers whose squares sum to `n`."
  @spec decompose(non_neg_integer()) :: [non_neg_integer()]
  def decompose(n) when is_integer(n) and n >= 0, do: search(n, 4)

  @spec search(non_neg_integer(), 2 | 3 | 4) :: [non_neg_integer()] | nil
  defp search(n, 2), do: pair(n, 0, root(n))

  defp search(n, count) do
    if count == 3 and not three?(n), do: nil, else: trial(n, count, root(n))
  end

  @spec trial(non_neg_integer(), 3 | 4, integer()) :: [non_neg_integer()] | nil
  defp trial(_n, _count, candidate) when candidate < 0, do: nil

  defp trial(n, count, candidate) do
    case search(n - candidate * candidate, count - 1) do
      nil -> trial(n, count, candidate - 1)
      rest -> [candidate | rest]
    end
  end

  @spec pair(non_neg_integer(), non_neg_integer(), integer()) :: [non_neg_integer()] | nil
  defp pair(_n, a, b) when a > b, do: nil

  defp pair(n, a, b) do
    sum = a * a + b * b

    cond do
      sum == n -> [a, b]
      sum < n -> pair(n, a + 1, b)
      sum > n -> pair(n, a, b - 1)
    end
  end

  # Legendre's obstruction avoids searching for three squares when none exist.
  @spec three?(non_neg_integer()) :: boolean()
  defp three?(n) when n > 0 and rem(n, 4) == 0, do: three?(div(n, 4))
  defp three?(n), do: rem(n, 8) != 7

  @spec root(non_neg_integer()) :: non_neg_integer()
  defp root(n) when n < 2, do: n
  defp root(n), do: root(n, Integer.pow(2, div(length(Integer.digits(n, 2)) + 1, 2)))

  @spec root(non_neg_integer(), pos_integer()) :: non_neg_integer()
  defp root(n, guess) do
    next = div(guess + div(n, guess), 2)
    if next >= guess, do: guess, else: root(n, next)
  end
end
