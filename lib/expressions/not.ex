defmodule Expressions.Not do
  @expression :not

  @spec parse(any()) :: Expression.t()
  def parse(condition_ast) do
   condition_expression = Generator.Expressions.generate_expression(condition_ast, %{}, %{}, 0)
    %Expression{lines: expression_lines} = condition_expression
    expression_line = Enum.at(expression_lines, 0)

    line = "~#{expression_line}"

    %Expression{name: @expression, lines: [line]}
  end
end
