defmodule Models.Expression do
  @moduledoc """
  Base type for defining an expression
  """

  use TypedStruct

  typedstruct do
    @typedoc "Type for a condition"
  end

  # Should be Models.Expression.t()
  @callback parse_expression(Models.Function.Clause.Metadata.t(), any()) :: any()

  # Should be List[Models.Expression.t()]
  @spec parse_expressions(Models.Function.Clause.Metadata.t(), any()) :: List[any()]
  def parse_expressions(metadata, body_ast) do
    IO.inspect(metadata)

    {_, expressions} =
      Macro.postwalk(body_ast, [], fn node, acc ->
        expression =
          case node do
            # Parse `if` expression
            {:if, _, _} = if_ast ->
              Models.Expression.If.parse_expression(metadata, if_ast)

            # Parse `return value` expression
            [do: {_value, _, nil} = return_value_ast] ->
              Models.Expression.Return.Value.parse_expression(metadata, return_value_ast)

            [else: {_value, _, nil} = return_value_ast] ->
              Models.Expression.Return.Value.parse_expression(metadata, return_value_ast)

            # Parse `return function` expression
            [do: {_function, _, [_, _]} = return_function_ast] ->
              Models.Expression.Return.Function.parse_expression(metadata, return_function_ast)

            [else: {_function, _, [_, _]} = return_function_ast] ->
              Models.Expression.Return.Function.parse_expression(metadata, return_function_ast)

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

    IO.inspect(expressions)
    expressions
  end
end
