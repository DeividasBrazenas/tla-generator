defmodule Tla.Generator.Models.Function.Spec do
  use TypedStruct

  typedstruct do
    @typedoc "Type for a function spec"

    field(:name, atom(), default: nil, enforce: true)
    field(:argument_types, List[atom()], default: [])
    field(:return_type, atom(), default: nil)
  end

  @spec get(any) :: List[Tla.Generator.Models.Function.Spec.t()]
  def get(ast) do
    {_, specs} = Macro.postwalk(ast, [], &get_spec/2)
    specs
  end

  @spec get_spec(any, List[Tla.Generator.Models.Function.Spec.t()]) :: {any, List[Tla.Generator.Models.Function.Spec.t()]}
  defp get_spec(
         {:spec, _, [{:"::", _, [{method, _, arguments}, {return_type, _, _}]}]} = node,
         acc
       ) do
    spec = %Tla.Generator.Models.Function.Spec{
      name: method,
      argument_types: Enum.map(arguments, fn {argument_type, _, _} -> argument_type end),
      return_type: return_type
    }

    {node, acc ++ [spec]}
  end

  defp get_spec(node, acc), do: {node, acc}
end
