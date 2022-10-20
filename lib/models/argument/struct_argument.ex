defmodule Models.Argument.Struct do
  @moduledoc """
  Defines a constant argument
  """
  @behaviour Models.Argument

  use TypedStruct

  typedstruct do
    field(:name, atom(), default: nil)
    field(:type, atom(), default: nil, enforce: true)
    field(:arguments, Models.Argument.Map.t(), default: nil)
  end

  @impl Models.Argument
  @spec parse_argument(any(), any()) :: Models.Argument.Struct.t()
  def parse_argument(
        [{:__aliases__, _, [type]}, {:%{}, _, arguments_map_ast}],
        %{
          name: name
        }
      ) do
    arguments_map = Models.Argument.Map.parse_argument(arguments_map_ast, nil)

    argument = %Models.Argument.Struct{
      name: name,
      type: type,
      arguments: arguments_map
    }

    argument
  end
end
