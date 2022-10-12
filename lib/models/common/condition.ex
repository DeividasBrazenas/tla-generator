defmodule Models.Common.Condition do
  @moduledoc """
  Module defining a condition for expression
  """
  use TypedStruct

  typedstruct do
    @typedoc "Type for a condition"

    field(:operator, atom(), default: nil, enforce: true)
    field(:left_operand, atom(), default: nil, enforce: true)
    field(:right_operand, atom(), default: nil, enforce: true)
  end

  @spec parse_condition(any()) :: Models.Common.Condition.t()
  def parse_condition({operator, _, [{left, _, _}, {right, _, _}]}) do
    condition = %Models.Common.Condition{
      operator: operator,
      left_operand: left,
      right_operand: right
    }

    condition
  end
end
