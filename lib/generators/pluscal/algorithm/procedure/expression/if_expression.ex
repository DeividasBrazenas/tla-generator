defmodule Generators.PlusCal.Algorithm.Procedure.Expression.If do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Algorithm.Procedure.Expression

  @impl Generators.PlusCal.Algorithm.Procedure.Expression
  @spec generate_expression(any(), Integer.t()) :: List[String.t()]
  def generate_expression(%Models.Expression.If{} = expression, indent_level) do
    expression =
      [
        "#{Indent.build(indent_level)}if #{Generators.Common.Condition.generate_condition(expression.condition)} then"
      ] ++
        generate_condition_satisfied_expressions(expression.condition_satisfied_expressions, indent_level + 1) ++
        generate_condition_unsatisfied_expressions(
          expression.condition_unsatisfied_expressions,
          indent_level + 1
        ) ++
        [
          "#{Indent.build(indent_level)}end if;"
        ]

    expression
  end

  @spec generate_condition_satisfied_expressions(List[Models.Expression.t()], Integer.t()) ::
          List[String.t()]
  defp generate_condition_satisfied_expressions(expressions, indent_level) do
    Generators.PlusCal.Algorithm.Procedure.Expression.generate_expressions(expressions, indent_level)
  end

  @spec generate_condition_unsatisfied_expressions(List[Models.Expression.t()], Integer.t()) ::
          List[String.t()]
  defp generate_condition_unsatisfied_expressions(expressions, indent_level) do
    if length(expressions) > 0 do
      ["#{Indent.build(indent_level - 1)}else"] ++
        Generators.PlusCal.Algorithm.Procedure.Expression.generate_expressions(expressions, indent_level)
    else
      []
    end
  end
end
