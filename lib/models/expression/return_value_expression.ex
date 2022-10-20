defmodule Models.Expression.Return.Value do
  @moduledoc """
  Defines `if` expression
  """
  @behaviour Models.Expression

  use TypedStruct

  typedstruct do
    field(:value, atom(), default: nil, enforce: true)
    field(:function_name, atom(), default: nil, enforce: true)
  end

  @impl Models.Expression
  @spec parse_expression(any(), Models.Function.Clause.Metadata.t()) :: Models.Expression.Return.Value.t()
  def parse_expression({value, _, nil}, metadata) do
    expression = %Models.Expression.Return.Value{
      value: value,
      function_name: metadata.name
    }

    expression
  end
end