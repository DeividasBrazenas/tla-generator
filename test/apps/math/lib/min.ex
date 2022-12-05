defmodule Min do
  use Extractors.PlusCal

  @pluscal_procedure :min
  @spec min(integer(), integer()) :: integer()
  def min(a, b) when a > b, do: b
  def min(a, _), do: a
end
