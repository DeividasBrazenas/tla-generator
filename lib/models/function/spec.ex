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
  @spec parse_specs(List[atom()], List[atom()], any()) :: List[Models.Function.Spec.t()]
  def parse_specs(pluscal_processes, pluscal_procedures, ast) do
    {_, specs} = Macro.postwalk(ast, [], &parse_spec/2)

    filtered_specs =
      specs
      |> Enum.filter(fn spec -> Enum.member?(pluscal_processes, spec.name) || Enum.member?(pluscal_procedures, spec.name) end)

    filtered_specs
  end

  @spec parse_spec(any(), List[Models.Function.Spec.t()]) ::
          {any(), List[Models.Function.Spec.t()]}
  defp parse_spec(
         # Return type is ignored. Probably it is not needed for PlusCal
         {:spec, _, [{:"::", _, [{method, _, _arguments}, _]}]} = node,
         acc
       ) do
    IO.inspect(node)

    spec = %Models.Function.Spec{
      name: method,
      #argument_types: Enum.map(arguments, fn {argument_type, _, _} -> argument_type end),
      argument_types: [], # Maybe it is also not needed?
      return_type: nil
    }

    {node, acc ++ [spec]}
  end

  defp parse_spec(node, acc), do: {node, acc}
end
