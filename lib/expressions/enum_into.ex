defmodule Expressions.EnumInto do
  alias Common.Indent, as: Indent
  @expression :enum_into

  @spec parse(atom(), atom(), any(), any(), Integer.t()) :: Expression.t()
  def parse(variable, enumerable, {iterator, _, nil}, action_ast, indent_lvl) do
    action = parse_action(variable, action_ast)

    line =
      "#{Indent.build(indent_lvl)}#{variable} := [#{iterator} \\in #{enumerable} |-> #{action}];"

    %Expression{name: @expression, lines: [line], variables: [Atom.to_string(variable)]}
  end

  @spec parse_action(atom(), any()) :: String.t()
  defp parse_action(variable, {{key, _, nil}, [value]}) do
    action_expression = Generator.Expressions.generate_expression(value, %{}, %{}, 0)

    %Expression{lines: action_lines} = action_expression
    action = Enum.at(action_lines, 0)

    "#{variable}[#{key}] \\cup {#{action}}"
  end
end
