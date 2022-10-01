defmodule Gcd do
  use PlusCal.Extractor

  @tla_generation_defs :gcd
  @spec gcd(integer(), integer()) :: integer()
  def gcd(x, y) when x == y, do: x
  def gcd(x, y) when x > y, do: gcd(x - y, y)
  def gcd(x, y) when x < y, do: gcd(x, y - x)
end
