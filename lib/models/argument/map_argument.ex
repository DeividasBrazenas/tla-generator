defmodule Models.Argument.Map do
  @moduledoc """
  Defines a constant argument
  """
  @behaviour Models.Argument

  use TypedStruct

  typedstruct do
    field(:key_value_pairs, List[{atom(), Models.Argument.t()}], default: nil, enforce: true)
    field(:name, atom(), default: nil)
  end

  @impl Models.Argument
  @spec parse_argument(any(), any()) :: Models.Argument.Map.t()
  def parse_argument(arguments_ast, %{name: name}) do
    key_value_pairs =
      arguments_ast
      |> Enum.map(fn {key, value} ->
        {key, Models.Argument.parse_argument(value)}
      end)

    argument = %Models.Argument.Map{
      key_value_pairs: key_value_pairs,
      name: name
    }

    argument
  end

  @impl Models.Argument
  @spec has_constant(Models.Argument.t()) :: boolean()
  def has_constant(argument) do
    {_, map_arguments} =
      Enum.map_reduce(argument.key_value_pairs, [], fn {_, argument}, acc ->
        {argument, acc ++ [argument]}
      end)

    constants = Models.Argument.get_arguments_with_constants(map_arguments)
    has_constants = length(constants) > 0
    has_constants
  end
end
