defmodule Max do
  use Extractors.TLA

  @tla_defs :operation

  @spec max(integer, integer) :: integer
  def max(a, b) when a < b, do: b
  def max(a, _), do: a
end