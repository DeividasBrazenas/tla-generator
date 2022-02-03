defmodule FunctionModel do
  defstruct [:spec, :arguments, :cases]

  @spec getFunctions(List[FunctionSpecModel], List[FunctionBodyModel]) :: List[FunctionModel]
  def getFunctions(specs, functionBodies) do
    functions =
      Enum.map(specs, fn spec ->
        filteredFunctions = Enum.filter(functionBodies, fn body -> body.name === spec.name end)

        %FunctionModel{
          spec: spec,
          arguments: getArguments(Enum.map(filteredFunctions, fn func -> func.arguments end)),
          cases:
            getCases(Enum.map(filteredFunctions, fn func -> {func.condition, func.return} end))
        }
      end)

    functions
  end

  @spec getArguments(List[List[atom()]]) :: List[atom()]
  defp getArguments(argsList) do
    arguments =
      Enum.filter(argsList, fn args -> !Enum.any?(args, fn arg -> arg === :_ end) end)
      |> Enum.at(0)

    arguments
  end

  defp getCases(cases) do
    orderedCases =
      Enum.sort_by(cases, fn {condition, _} -> condition end)
      |> Enum.reverse()
      |> Enum.reduce([], fn {condition, return}, acc ->
        if condition != nil do
          acc ++ [{condition, return}]
        else
          previousConditions = Enum.map(acc, fn {condition, _} -> condition end)
          oppositeCondition = getOppositeCondition(previousConditions)

          acc ++ [{oppositeCondition, return}]
        end
      end)

    orderedCases
  end

  defp getOppositeCondition(conditions) do
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

    oppositeCondition = %FunctionConditionModel{
      left_operand: condition.left_operand,
      operator: oppositeOperator,
      right_operand: condition.right_operand
    }

    oppositeCondition
  end
end
