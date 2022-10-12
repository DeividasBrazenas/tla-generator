defmodule Generators.PlusCal.Algorithm.Procedure.Expression.Return.Value do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Algorithm.Procedure.Expression

  @impl Generators.PlusCal.Algorithm.Procedure.Expression
  @spec generate_expression(any(), Integer.t()) :: List[String.t()]
  def generate_expression(%Models.Expression.Return.Value{} = expression, indent_level) do
    [
      "#{Indent.build(indent_level)}result_#{expression.function_name} := #{expression.value};",
      "#{Indent.build(indent_level)}return;"
    ]
  end
end
