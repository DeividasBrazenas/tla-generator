defmodule Generators.PlusCal.Expression.Call.Function do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Expression

  @impl Generators.PlusCal.Expression
  @spec generate_expression(any(), List[Models.Type.t()], List[atom()], Integer.t()) :: List[String.t()]
  def generate_expression(
        %Models.Expression.Call.Function{} = expression,
        fn_inputs,
        local_variables,
        indent_level
      ) do
    arguments =
      expression.argument_names
      |> Enum.map(fn arg -> Generators.Common.Argument.get_accessor(arg, fn_inputs, local_variables) end)

    IO.inspect(expression)

    [
      "#{Indent.build(indent_level)}await #{expression.function_name}(#{Enum.join(arguments, ", ")});",
      "#{Indent.build(indent_level)}#{expression.variable_name} := result_#{expression.function_name};",
      ""
    ]
  end
end
