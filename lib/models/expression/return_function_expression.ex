defmodule Models.Expression.Return.Function do
  @moduledoc """
  Defines `return function` expression
  """
  @behaviour Models.Expression

  use TypedStruct

  typedstruct do
    field(:parent_function_name, atom(), default: nil, enforce: true)
    field(:namespace, atom(), default: nil, enforce: true)
    field(:function_name, atom(), default: nil, enforce: true)
    field(:arguments, List[any()], default: [], enforce: true)
  end

  @impl Models.Expression
  @spec parse_expression(any(), Models.Function.Clause.Metadata.t()) ::
          Models.Expression.Return.Function.t()
  def parse_expression(
        {{:., _, function_call_ast}, _, arguments_ast},
        metadata
      ) do
    arguments = arguments_ast |> Enum.map(fn ast -> get_argument(ast) end)
    namespace = List.first(function_call_ast)
    function_name = List.last(function_call_ast)

    expression = %Models.Expression.Return.Function{
      parent_function_name: metadata.name,
      namespace: namespace,
      function_name: function_name,
      arguments: arguments
    }

    expression
  end

  def parse_expression(_ast, _metadata), do: nil

  defp get_argument(ast) do
    Macro.to_string(ast)
  end
end
