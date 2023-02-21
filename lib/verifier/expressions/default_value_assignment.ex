defmodule Verifier.Expressions.DefaultValueAssignment do
  alias Common.Indent, as: Indent

  def convert(variable, variable_declarations, indent_lvl) do
    default_value = get_default_value(variable, variable_declarations)
    code = "#{Indent.build(indent_lvl)}#{variable} = #{default_value}"

    code
  end

  defp get_default_value(variable, variable_declarations) do
    variable_declarations
    |> Enum.reduce(nil, fn declaration, acc ->
      if acc != nil do
        acc
      else
        cond do
          Regex.run(~r/^ *#{variable} = .*({}).*$/, declaration) != nil -> "%{}"
          true -> nil
        end
      end
    end)
  end
end
