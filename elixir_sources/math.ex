defmodule Math do
  #use Extractors.TLA
  #@tla_defs :operation

  @spec min(integer, integer) :: integer
  def min(a, b) when a > b, do: b
  def min(a, _), do: a

  @spec max(integer, integer) :: integer
  def max(a, b) when a < b, do: b
  def max(a, _), do: a
end
