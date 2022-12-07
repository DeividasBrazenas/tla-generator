defmodule Models.Expression.Call.ExternalFunction do
  @moduledoc """
  Defines `value update` expression
  """
  @behaviour Models.Expression

  use TypedStruct

  typedstruct do
    field(:variables, List[atom()], default: [])
    field(:namespace, atom(), default: nil, enforce: true)
    field(:function_name, atom(), default: nil, enforce: true)
    field(:arguments, List[any()], default: [], enforce: true)
  end

  @impl Models.Expression
  @spec parse_expression(any(), Models.Function.Clause.Metadata.t()) ::
          Models.Expression.Call.ExternalFunction.t()
  def parse_expression(
        {:=, _, [variables_ast, {{:., _, function_call_ast}, _, arguments_ast}]},
        _metadata
      ) do
    variables = Models.Type.parse_type(variables_ast)
    arguments = arguments_ast |> Enum.map(fn ast -> get_argument(ast) end)
    namespace = List.first(function_call_ast)
    function_name = List.last(function_call_ast)

    expression = %Models.Expression.Call.ExternalFunction{
      variables: variables,
      namespace: namespace,
      function_name: function_name,
      arguments: arguments
    }

    expression
  end

  defp get_argument(ast) do
    Macro.to_string(ast)
  end
end
