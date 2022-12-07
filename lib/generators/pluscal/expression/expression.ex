defmodule Generators.PlusCal.Expression do
  @callback generate_expression(any(), List[Models.Type.t()], List[atom()], Integer.t()) ::
              List[String.t()]

  @spec generate_expressions(
          List[Models.Expression.t()],
          List[Models.Type.t()],
          List[String.t()],
          Integer.t()
        ) :: List[String.t()]
  def generate_expressions(expression_models, fn_arguments, local_variables, indent_level) do
    expressions =
      expression_models
      |> Enum.flat_map(fn expression ->
        case expression do
          %Models.Expression.If{} ->
            Generators.PlusCal.Expression.If.generate_expression(
              expression,
              fn_arguments,
              local_variables,
              indent_level
            )

          %Models.Expression.Map.Update{} ->
            Generators.PlusCal.Expression.Map.Update.generate_expression(
              expression,
              fn_arguments,
              local_variables,
              indent_level
            )

          %Models.Expression.Call.Function{} ->
            Generators.PlusCal.Expression.Call.Function.generate_expression(
              expression,
              fn_arguments,
              local_variables,
              indent_level
            )

          %Models.Expression.Call.ExternalFunction{} ->
            Generators.PlusCal.Expression.Call.ExternalFunction.generate_expression(
              expression,
              fn_arguments,
              local_variables,
              indent_level
            )

          %Models.Expression.Return.Value{} ->
            Generators.PlusCal.Expression.Return.Value.generate_expression(
              expression,
              fn_arguments,
              local_variables,
              indent_level
            )

          %Models.Expression.Return.Function{} ->
            Generators.PlusCal.Expression.Return.Function.generate_expression(
              expression,
              fn_arguments,
              local_variables,
              indent_level
            )
        end
      end)

    expressions
  end
end
