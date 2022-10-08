defmodule Math do
  use Extractors.PlusCal

  @tla_generation_defs :min
  @spec min(integer(), integer()) :: integer()
  def min(a, b) when a > b, do: b
  def min(a, _), do: a

  @tla_generation_defs :max
  @spec max(integer(), integer()) :: integer()
  def max(a, b) when a < b, do: b
  def max(a, _), do: a
end
