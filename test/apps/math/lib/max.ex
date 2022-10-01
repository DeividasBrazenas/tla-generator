defmodule Max do
  use PlusCal.Extractor

  @tla_generation_defs :max
  @spec max(integer(), integer()) :: integer()
  def max(a, b) when a < b, do: b
  def max(a, _), do: a

  @spec foo(integer(), integer()) :: integer()
  def foo(a, b) when a < b, do: b

  @spec bar(integer(), integer()) :: integer()
  def bar(a, b) when a < b, do: b
end
