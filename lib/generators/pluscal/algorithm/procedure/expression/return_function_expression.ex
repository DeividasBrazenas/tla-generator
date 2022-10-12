defmodule Generators.PlusCal.Algorithm.Procedure.Expression.Return.Function do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Algorithm.Procedure.Expression

  @impl Generators.PlusCal.Algorithm.Procedure.Expression
  @spec generate_expression(any(), Integer.t()) :: List[String.t()]
  def generate_expression(%Models.Expression.Return.Function{} = expression, indent_level) do
    [
      "#{Indent.build(indent_level)}call #{expression.function_call}"
    ]
  end
end
