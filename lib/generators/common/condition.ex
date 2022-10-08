defmodule Generators.Common.Condition do
  # Returns TLA+ condition string
  @spec generate_condition(Models.Common.Condition.t()) :: String.t()
  def generate_condition(condition) do
    "#{condition.left_operand} #{get_pluscal_operator(condition.operator)} #{condition.right_operand}"
  end

  @spec get_pluscal_operator(atom()) :: String.t()
  defp get_pluscal_operator(operator) do
    case operator do
      :== -> "="
      :!= -> "#"
      :< -> "<"
      :> -> ">"
      :<= -> "<="
      :>= -> ">="
    end
  end
end
