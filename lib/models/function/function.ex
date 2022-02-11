defmodule Function.Function do
  use TypedStruct

  typedstruct do
    @typedoc "Type for a function body"

    field(:spec, Tla.Generator.Models.Function.Spec.t(), default: nil, enforce: true)
    field(:arguments, List[atom()], default: [])
    field(:cases, List[Tla.Generator.Models.Function.Case.t()], default: nil)
  end

  @spec get(List[Funcion.Spec.t()], any) :: List[Function.Function.t()]
  def get(specs, ast) do
    bodies = Tla.Generator.Models.Function.Body.get(ast)

    functions =
      Enum.map(specs, fn spec ->
        filtered_functions = Enum.filter(bodies, fn body -> body.name === spec.name end)

        %Function.Function{
          spec: spec,
          arguments: get_arguments(Enum.map(filtered_functions, fn func -> func.arguments end)),
          cases:
            Tla.Generator.Models.Function.Case.get(
              Enum.map(filtered_functions, fn func ->
                %Tla.Generator.Models.Function.Case{
                  condition: func.condition,
                  return: func.return
                }
              end)
            )
        }
      end)

    functions
  end

  @spec get_arguments(List[List[atom()]]) :: List[atom()]
  defp get_arguments(args_list) do
    arguments =
      Enum.filter(args_list, fn args -> !Enum.any?(args, fn arg -> arg === :_ end) end)
      |> Enum.at(0)

    arguments
  end
end
