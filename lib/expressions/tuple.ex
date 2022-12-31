defmodule Expressions.Tuple do
  @expression :tuple

  @spec parse(any(), Map.t(), Integer.t()) :: Expression.t()
  def parse(arguments_ast, expressions_counter, indent_lvl) do
    arguments =
      arguments_ast
      |> Enum.map(fn arg ->
        expression = Generator.Expressions.generate_expression(arg, expressions_counter, %{}, indent_lvl)
        %Expression{lines: lines} = expression
        Enum.at(lines, 0)
      end)

    %Expression{name: @expression, lines: ["<<#{Enum.join(arguments, ", ")}>>"]}
  end
end
