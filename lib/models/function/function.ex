defmodule Function.Function do
  defstruct [:spec, :arguments, :cases]

  def getFunctions(specs, ast) do
    functionBodies = Function.Body.getFunctionBodies(ast)

    functions =
      Enum.map(specs, fn spec ->
        filteredFunctions = Enum.filter(functionBodies, fn body -> body.name === spec.name end)

        %Function.Function{
          spec: spec,
          arguments: getArguments(Enum.map(filteredFunctions, fn func -> func.arguments end)),
          cases:
            Function.Case.getCases(
              Enum.map(filteredFunctions, fn func -> {func.condition, func.return} end)
            )
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
end
