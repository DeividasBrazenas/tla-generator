defmodule Expressions.CustomPredicateCall do
  @expression :custom_predicate_call
  # This expression is used for translating "predicate.(value)"

  @spec parse(any) :: Expression.t()
  def parse(arguments_ast) do
    arguments_expression = Generator.Expressions.generate_expression(arguments_ast, %{}, %{}, 0)
    %Expression{lines: argument_lines} = arguments_expression
    argument_line = Enum.at(argument_lines, 0)

    line = ["predicate[#{argument_line}]"]
    expression = %Expression{name: @expression, lines: [line]}
    expression
  end
end
