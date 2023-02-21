defmodule Verifier.Expressions.MapGet do
  alias Common.Indent, as: Indent

  def convert(variable, map_variable, key, indent_lvl) do
    code =
      "#{Indent.build(indent_lvl)}#{variable} = Map.get(#{map_variable}, #{Verifier.Helpers.map_type(key)}, %{})"

    code
  end
end
