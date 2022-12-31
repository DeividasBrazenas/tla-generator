defmodule Common.Indent do
  @indent_space_count 2

  @spec build(Integer.t()) :: String.t()
  def build(indent_level) do
    indent = String.duplicate(" ", indent_level * @indent_space_count)
    indent
  end
end
