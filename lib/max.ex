defmodule Max do
  use ExTla
  def max(a, b) when a < b, do: b
  def max(a, _), do: a
end
