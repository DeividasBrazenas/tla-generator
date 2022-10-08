defmodule Gcd do
  use Extractors.PlusCal

  @tla_generation_defs :gcd
  @spec gcd(integer(), integer()) :: integer()
  def gcd(x, y) when x > y, do: gcd(x - y, y)
  def gcd(x, y) when x < y, do: gcd(x, y - x)
  def gcd(x, y) when x == y, do: x
end
