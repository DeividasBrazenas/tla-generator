defmodule Models.Type.Tuple do
  @moduledoc """
  Defines a constant argument
  """
  @behaviour Models.Type

  use TypedStruct

  typedstruct do
    field(:arguments, List[{integer(), Models.Type.t()}], default: nil, enforce: true)
    field(:name, atom(), default: nil)
  end

  @impl Models.Type
  @spec parse_type(any(), any()) :: Models.Type.Tuple.t()
  def parse_type(arguments_ast, %{name: name}) do
    tuple_arguments =
      arguments_ast
      |> Enum.with_index(fn argument_ast, idx -> {idx + 1, Models.Type.parse_type(argument_ast)}
      end)

    argument = %Models.Type.Tuple{
      arguments: tuple_arguments,
      name: name
    }

    argument
  end

  @impl Models.Type
  @spec has_constant(Models.Type.Tuple.t()) :: boolean()
  def has_constant(argument) do
    constants = Models.Type.get_arguments_with_constants(Enum.map(argument.arguments, fn {_idx, arg} -> arg end))
    has_constants = length(constants) > 0
    has_constants
  end
end
