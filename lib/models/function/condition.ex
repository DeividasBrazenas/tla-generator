defmodule Tla.Generator.Models.Function.Condition do
  use TypedStruct

  typedstruct do
    @typedoc "Type for a condition"

    field(:operator, atom(), default: nil, enforce: true)
    field(:left_operand, atom(), default: nil, enforce: true)
    field(:right_operand, atom(), default: nil, enforce: true)
  end

  @spec get(any) :: Tla.Generator.Models.Function.Condition.t()
  def get({operator, _, [{left, _, _}, {right, _, _}]}) do
    condition = %Tla.Generator.Models.Function.Condition{
      operator: operator,
      left_operand: left,
      right_operand: right
    }

    condition
  end

  @spec get_opposite_condition(List[Tla.Generator.Models.Function.Condition.t()]) :: Tla.Generator.Models.Function.Condition.t()
  def get_opposite_condition(conditions) do
    # This will need to handle several conditions (eg: oposite of :> and :< is :== )
    condition = List.last(conditions)

    opposite_operator =
      case condition.operator do
        :< -> :>=
        :<= -> :>
        :> -> :<=
        :>= -> :<
        :== -> :!=
        :=== -> :!==
        :!= -> :==
        :!== -> :===
      end

    opposite_condition = %Tla.Generator.Models.Function.Condition{
      left_operand: condition.left_operand,
      operator: opposite_operator,
      right_operand: condition.right_operand
    }

    opposite_condition
  end
end
