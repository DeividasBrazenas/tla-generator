defmodule Tla.Generator.Footer do
  @spec get(String.t()) :: String.t()
  def get(module_name) do
    length = 33 + 33 + 6 + 3 + String.length(module_name)
    String.duplicate("=", length)
  end
end
