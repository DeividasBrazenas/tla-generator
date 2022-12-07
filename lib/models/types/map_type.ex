defmodule Models.Type.Map do
  @moduledoc """
  Defines a constant argument
  """
  @behaviour Models.Type

  use TypedStruct

  typedstruct do
    field(:key_value_pairs, List[{atom(), Models.Type.t()}], default: [], enforce: true)
    field(:name, atom(), default: nil)
  end

  @impl Models.Type
  @spec parse_type(any(), any()) :: Models.Type.Map.t()
  def parse_type(arguments_ast, %{name: name}) do
    key_value_pairs =
      arguments_ast
      |> Enum.map(fn {key, value} ->
        {key, Models.Type.parse_type(value)}
      end)

    argument = %Models.Type.Map{
      key_value_pairs: key_value_pairs,
      name: name
    }

    argument
  end

  @impl Models.Type
  @spec has_constant(Models.Type.t()) :: boolean()
  def has_constant(argument) do
    {_, map_arguments} =
      Enum.map_reduce(argument.key_value_pairs, [], fn {_, argument}, acc ->
        {argument, acc ++ [argument]}
      end)

    constants = Models.Type.get_arguments_with_constants(map_arguments)
    has_constants = length(constants) > 0
    has_constants
  end
end
