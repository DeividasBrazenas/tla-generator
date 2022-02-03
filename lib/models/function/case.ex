defmodule Function.Case do
  defstruct [:condition, :return]

  def getCases(cases) do
    orderedCases =
      Enum.sort_by(cases, fn {condition, _} -> condition end)
      |> Enum.reverse()
      |> Enum.reduce([], fn {condition, return}, acc ->
        if condition != nil do
          acc ++ [{condition, return}]
        else
          previousConditions = Enum.map(acc, fn {condition, _} -> condition end)
          oppositeCondition = Function.Condition.getOppositeCondition(previousConditions)

          acc ++ [{oppositeCondition, return}]
        end
      end)

    orderedCases
  end
end
