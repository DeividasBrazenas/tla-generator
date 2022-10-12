defmodule Models.Expression.Return.Function do
  @moduledoc """
  Defines `if` expression
  """
  @behaviour Models.Expression

  use TypedStruct

  typedstruct do
    field(:function_call, String.t(), default: nil, enforce: true)
    field(:arguments, List[any()], default: [])
  end

  @impl Models.Expression
  # Should be Models.Expression.If.t()
  @spec parse_expression(Models.Function.Case.Metadata.t(), any()) :: any()
  def parse_expression(_, return_ast) do
    function_call = Macro.to_string(return_ast)

    expression = %Models.Expression.Return.Function{
      function_call: function_call
    }

    expression
  end
end
