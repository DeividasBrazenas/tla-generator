defmodule Models.Function.Spec do
  @moduledoc """
  Module defining the function's specification
  """
  use TypedStruct

  typedstruct do
    field(:name, atom(), default: nil, enforce: true)
    field(:argument_types, List[atom()], default: [])
    field(:return_type, atom(), default: nil)
  end

  @doc """
  Parses specs that are specified in generation_defs
  """
  @spec parse_specs(List[atom()], any()) :: List[Models.Function.Spec.t()]
  def parse_specs(generation_defs, ast) do
    {_, specs} = Macro.postwalk(ast, [], &parse_spec/2)

    filtered_specs =
      specs
      |> Enum.filter(fn spec -> Enum.member?(generation_defs, spec.name) end)

    filtered_specs
  end

  @spec parse_spec(any(), List[Models.Function.Spec.t()]) ::
          {any(), List[Models.Function.Spec.t()]}
  defp parse_spec(
         {:spec, _, [{:"::", _, [{method, _, arguments}, {return_type, _, _}]}]} = node,
         acc
       ) do
    spec = %Models.Function.Spec{
      name: method,
      argument_types: Enum.map(arguments, fn {argument_type, _, _} -> argument_type end),
      return_type: return_type
    }

    {node, acc ++ [spec]}
  end

  defp parse_spec(node, acc), do: {node, acc}
end
