defmodule Min do
  def min(a, b) when a > b, do: b
  def min(a, _), do: a
end
