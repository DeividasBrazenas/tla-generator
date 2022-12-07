defmodule Models.Expression.Return.Value do
  @moduledoc """
  Defines `return value` expression
  """
  @behaviour Models.Expression

  use TypedStruct

  typedstruct do
    field(:parent_function_name, atom(), default: nil, enforce: true)
    field(:value, Models.Type.t(), default: nil, enforce: true)
  end

  @impl Models.Expression
  @spec parse_expression(any(), Models.Function.Clause.Metadata.t()) ::
          Models.Expression.Return.Value.t()
  def parse_expression(value, metadata) do
    expression = %Models.Expression.Return.Value{
      value: Models.Type.parse_type(value),
      parent_function_name: metadata.name
    }

    expression
  end
end
