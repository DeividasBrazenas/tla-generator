defmodule Generators.PlusCal.Algorithm.Procedure.Expression do
  @callback generate_expression(any(), List[Models.Argument.t()], Integer.t()) :: List[String.t()]

  @spec generate_expressions(List[Models.Expression.t()], List[Models.Argument.t()], Integer.t()) :: List[String.t()]
  def generate_expressions(expression_models, fn_arguments, indent_level) do
    expressions =
      expression_models
      |> Enum.flat_map(fn expression ->
        case expression do
          %Models.Expression.If{} -> Generators.PlusCal.Algorithm.Procedure.Expression.If.generate_expression(expression, fn_arguments, indent_level)
          %Models.Expression.Map.Update{} -> Generators.PlusCal.Algorithm.Procedure.Expression.Map.Update.generate_expression(expression, fn_arguments, indent_level)
          %Models.Expression.Call.Function{} -> Generators.PlusCal.Algorithm.Procedure.Expression.Call.Function.generate_expression(expression, fn_arguments, indent_level)
          %Models.Expression.Return.Value{} -> Generators.PlusCal.Algorithm.Procedure.Expression.Return.Value.generate_expression(expression, fn_arguments, indent_level)
          %Models.Expression.Return.Function{} -> Generators.PlusCal.Algorithm.Procedure.Expression.Return.Function.generate_expression(expression, fn_arguments, indent_level)
        end
      end)

    expressions
  end
end
