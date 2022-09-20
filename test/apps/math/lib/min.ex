defmodule Min do
  use Tla.Extractor
  @tla_generation_type :operation

  @tla_generation_defs :min
  @spec min(integer(), integer()) :: integer()
  def min(a, b) when a > b, do: b
  def min(a, _), do: a
end
