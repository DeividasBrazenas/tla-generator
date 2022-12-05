defmodule Models.Expression.Call.Function do
  @moduledoc """
  Defines `value update` expression
  """
  @behaviour Models.Expression

  use TypedStruct

  typedstruct do
    field(:variable_name, atom(), default: nil, enforce: true)
    field(:function_name, atom(), default: nil, enforce: true)
    field(:argument_names, List[atom()], default: [], enforce: true)
  end

  @impl Models.Expression
  @spec parse_expression(any(), Models.Function.Clause.Metadata.t()) ::
          Models.Expression.Call.Function.t()
  def parse_expression(
        {:=, _, [{variable_name, _, _}, {function_name, _, arguments_ast}]},
        _metadata
      ) do
    argument_names = arguments_ast |> Enum.map(fn ast -> get_argument_name(ast) end)

    expression = %Models.Expression.Call.Function{
      variable_name: variable_name,
      function_name: function_name,
      argument_names: argument_names
    }

    expression
  end

  @spec get_argument_name(any()) :: atom()
  defp get_argument_name({value, _, nil}) do
    value
  end
end
