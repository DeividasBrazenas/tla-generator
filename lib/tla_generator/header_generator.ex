defmodule Tla.Generator.Header do
  @spec get(String.t()) :: String.t()
  def get(module_name) do
    tlaValue = "#{String.duplicate("-", 33)} MODULE #{module_name} #{String.duplicate("-", 33)}"
    tlaValue
  end
end
