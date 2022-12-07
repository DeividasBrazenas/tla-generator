defmodule Generators.PlusCal.Expression.Return.Function do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Expression

  @impl Generators.PlusCal.Expression
  @spec generate_expression(any(), List[Models.Type.t()], List[atom()], Integer.t()) :: List[String.t()]
  def generate_expression(%Models.Expression.Return.Function{} = expression, _fn_inputs, _local_variables, indent_level) do
    [
      "#{Indent.build(indent_level)}await #{expression.namespace}.#{expression.function_name}(#{Enum.join(expression.arguments, ", ")})"
    ]
  end
end
