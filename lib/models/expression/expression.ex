defmodule Models.Expression do
  @moduledoc """
  Base type for defining an expression
  """

  use TypedStruct

  @type t() ::
          Models.Expression.If.t()
          | Models.Expression.Map.Update.t()
          | Models.Expression.Call.Function.t()
          | Models.Expression.Call.ExternalFunction.t()
          | Models.Expression.Return.Function.t()
          | Models.Expression.Return.Value.t()

  @callback parse_expression(any(), Models.Function.Clause.Metadata.t()) :: Models.Expression.t()

  @spec parse_expressions(any(), Models.Function.Clause.Metadata.t()) ::
          List[Models.Expression.t()]
  def parse_expressions(body_ast, metadata) do
    {_, expressions} =
      Macro.prewalk(body_ast, [], fn node, acc ->
        IO.inspect(node)

        expression =
          case node do
            # Parse `if` expression
            {:if, _, _} = if_ast ->
              Models.Expression.If.parse_expression(if_ast, metadata)

            # Parse `map update` expression
            {:=, _, [_, {_, _, [{:|, _, _}]}]} = map_update_ast ->
              Models.Expression.Map.Update.parse_expression(map_update_ast, metadata)

            # Parse `call external function` expression
            {:=, _, [_, {{:., _, _}, _, _}]} = call_external_function_ast ->
              Models.Expression.Call.ExternalFunction.parse_expression(
                call_external_function_ast,
                metadata
              )

            # Parse `call function` expression
            {:=, _, [_, {_, _, _}]} = call_function_ast ->
              Models.Expression.Call.Function.parse_expression(call_function_ast, metadata)

            # Parse `return value` expression
            [do: {_value, _, nil} = return_value_ast] ->
              Models.Expression.Return.Value.parse_expression(return_value_ast, metadata)

            [do: {:{}, _, values}] ->
              Models.Expression.Return.Value.parse_expression(values, metadata)

            [else: {_value, _, nil} = return_value_ast] ->
              Models.Expression.Return.Value.parse_expression(return_value_ast, metadata)

            {:{}, _, values} ->
              Models.Expression.Return.Value.parse_expression(values, metadata)

            {return, _, nil} ->
              Models.Expression.Return.Value.parse_expression(return, metadata)

            # Parse `return function` expression
            [do: {_function, _, _arguments} = return_function_ast] ->
              Models.Expression.Return.Function.parse_expression(
                return_function_ast,
                metadata
              )

            [else: {_function, _, [_, _]} = return_function_ast] ->
              Models.Expression.Return.Function.parse_expression(return_function_ast, metadata)

            # None of expressions are matched
            _ ->
              nil
          end

        new_node =
          case expression do
            nil -> node
            _ -> {}
          end

        new_acc =
          case expression do
            nil -> acc
            _ -> acc ++ [expression]
          end

        {new_node, new_acc}
      end)

    expressions
  end
end
