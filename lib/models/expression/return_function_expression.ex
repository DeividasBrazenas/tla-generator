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
  @spec parse_expression(any(), Models.Function.Clause.Metadata.t()) :: Models.Expression.Return.Function.t()
  def parse_expression(return_ast, _) do
    function_call = Macro.to_string(return_ast)

    expression = %Models.Expression.Return.Function{
      function_call: function_call
    }

    expression
  end
end
