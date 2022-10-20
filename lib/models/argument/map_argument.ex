defmodule Models.Argument.Map do
  @moduledoc """
  Defines a constant argument
  """
  @behaviour Models.Argument

  use TypedStruct

  typedstruct do
    field(:key_value_pairs, List[{atom(), any()}], default: nil, enforce: true)
    field(:name, atom(), default: nil)
  end

  @impl Models.Argument
  @spec parse_argument(any(), any()) :: Models.Argument.Map.t()
  def parse_argument(arguments_ast, _) do
    key_value_pairs =
      arguments_ast
      |> Enum.map(fn {key, value} ->
        {key, Models.Argument.parse_argument(value)}
      end)

    argument = %Models.Argument.Map{
      key_value_pairs: key_value_pairs
    }

    argument
  end
end
