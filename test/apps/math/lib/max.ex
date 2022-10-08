defmodule Max do
  use Extractors.PlusCal

  @tla_generation_defs :max
  @spec max(integer(), integer()) :: integer()
  def max(a, b) when a < b, do: b
  def max(a, _), do: a

  @tla_generation_defs :max_v2
  @spec max_v2(integer(), integer()) :: integer()
  def max_v2(a, b) do
    if a > b do
      a
    else
      b
    end
  end
end
