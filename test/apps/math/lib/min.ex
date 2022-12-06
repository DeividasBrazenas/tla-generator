defmodule Min do
  use Extractors.PlusCal

  @pluscal_process :min
  @spec min(integer(), integer()) :: integer()
  def min(a, b) when a > b, do: b
  def min(a, _), do: a
end
