defmodule Models.Argument.Tuple do
  @moduledoc """
  Defines a constant argument
  """
  @behaviour Models.Argument

  use TypedStruct

  typedstruct do
    field(:arguments, List[{integer(), Models.Argument.t()}], default: nil, enforce: true)
    field(:name, atom(), default: nil)
  end

  @impl Models.Argument
  @spec parse_argument(any(), any()) :: Models.Argument.Tuple.t()
  def parse_argument(arguments_ast, %{name: name}) do
    tuple_arguments =
      arguments_ast
      |> Enum.with_index(fn argument_ast, idx -> {idx + 1, Models.Argument.parse_argument(argument_ast)}
      end)

    argument = %Models.Argument.Tuple{
      arguments: tuple_arguments,
      name: name
    }

    argument
  end

  @impl Models.Argument
  @spec has_constant(Models.Argument.Tuple.t()) :: boolean()
  def has_constant(argument) do
    constants = Models.Argument.get_arguments_with_constants(Enum.map(argument.arguments, fn {_idx, arg} -> arg end))
    has_constants = length(constants) > 0
    has_constants
  end
end
