defmodule Min do
#  use Extractors.TLA
#  @tla_defs :operation

  @spec min(integer, integer) :: integer
  def min(a, b) when a > b, do: b
  def min(a, _), do: a
end
