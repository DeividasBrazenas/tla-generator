defmodule Expressions.MapGet do
  alias Common.Indent, as: Indent
  @expression :map_get

  @spec parse(atom(), atom(), any(), any(), Integer.t()) :: Expression.t()
  def parse(variable, map_variable, key_ast, _default_value_ast, indent_lvl) do
    key_expression = Generator.Expressions.generate_expression(key_ast, %{}, %{}, 0)
    %Expression{lines: key_lines} = key_expression
    key = Enum.at(key_lines, 0)

    line = "#{Indent.build(indent_lvl)}#{variable} := #{map_variable}[#{key}];"

    %Expression{name: @expression, lines: [line], variables: [Atom.to_string(variable)]}
  end
end
