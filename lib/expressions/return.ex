defmodule Expressions.Return do
  alias Common.Indent, as: Indent
  @expression :return

  @spec parse(List[any()], Map.t(), Integer.t()) :: Expression.t()
  def parse(arguments_ast, expressions_counter, indent_lvl) do
    expression =
      Generator.Expressions.generate_expression(
        arguments_ast,
        expressions_counter,
        %{},
        indent_lvl
      )

    %Expression{lines: lines} = expression

    return_line = "#{Indent.build(indent_lvl)}result := #{Enum.at(lines, 0)};"
    %Expression{name: @expression, lines: [return_line], variables: ["result"]}
  end
end
