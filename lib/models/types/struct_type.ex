defmodule Models.Type.Struct do
  @moduledoc """
  Defines a constant argument
  """
  @behaviour Models.Type

  use TypedStruct

  typedstruct do
    field(:name, atom(), default: nil)
    field(:type, atom(), default: nil, enforce: true)
    field(:arguments, Models.Type.Map.t(), default: nil)
  end

  @impl Models.Type
  @spec parse_type(any(), any()) :: Models.Type.Struct.t()
  def parse_type(
        [{:__aliases__, _, [type]}, {:%{}, _, arguments_map_ast}],
        %{
          name: name
        }
      ) do
    arguments_map = Models.Type.Map.parse_type(arguments_map_ast, %{name: nil})

    argument = %Models.Type.Struct{
      name: name,
      type: type,
      arguments: arguments_map
    }

    argument
  end

  @impl Models.Type
  @spec has_constant(Models.Type.Struct.t()) :: boolean()
  def has_constant(argument) do
    has_constant = Models.Type.Map.has_constant(argument.arguments)
    has_constant
  end
end
