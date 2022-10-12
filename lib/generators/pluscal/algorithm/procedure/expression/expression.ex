defmodule Generators.PlusCal.Algorithm.Procedure.Expression do
  @callback generate_expression(any(), Integer.t()) :: List[String.t()]

  @spec generate_expressions(List[Models.Expression.t()], Integer.t()) :: List[String.t()]
  def generate_expressions(expression_models, indent_level) do
    expressions =
      expression_models
      |> Enum.flat_map(fn expression ->
        case expression do
          %Models.Expression.If{} -> Generators.PlusCal.Algorithm.Procedure.Expression.If.generate_expression(expression, indent_level)
          %Models.Expression.Return.Value{} -> Generators.PlusCal.Algorithm.Procedure.Expression.Return.Value.generate_expression(expression, indent_level)
          %Models.Expression.Return.Function{} -> Generators.PlusCal.Algorithm.Procedure.Expression.Return.Function.generate_expression(expression, indent_level)
        end
      end)

    expressions
  end
end
