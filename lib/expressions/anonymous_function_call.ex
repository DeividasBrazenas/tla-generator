defmodule Expressions.AnonymousFunctionCall do
  @expression :anonymous_function_call

  @spec parse(atom(), any()) :: Expression.t()
  def parse(function_name, arguments_ast) do
    arguments =
      arguments_ast
      |> Enum.map(fn arg_ast ->
        arguments_expression = Generator.Expressions.generate_expression(arg_ast, %{}, %{}, 0)

        %Expression{lines: argument_lines} = arguments_expression
        Enum.at(argument_lines, 0)
      end)
      |> Enum.join(", ")

    line = ["#{function_name}_fn(#{arguments})"]
    expression = %Expression{name: @expression, lines: [line]}
    expression
  end
end
