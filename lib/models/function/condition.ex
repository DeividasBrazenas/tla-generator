defmodule Function.Condition do
  defstruct [:operator, :left_operand, :right_operand]

  def getOppositeCondition(conditions) do
    # This will need to handle several conditions (eg: oposite of :> and :< is :== )
    condition = List.last(conditions)

    oppositeOperator =
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

    oppositeCondition = %Function.Condition{
      left_operand: condition.left_operand,
      operator: oppositeOperator,
      right_operand: condition.right_operand
    }

    oppositeCondition
  end
end
