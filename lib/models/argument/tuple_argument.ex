defmodule Models.Argument.Tuple do
  @moduledoc """
  Defines a constant argument
  """
  @behaviour Models.Argument

  use TypedStruct

  typedstruct do
    field(:arguments, List[Models.Argument.t()], default: nil, enforce: true)
    field(:name, atom(), default: nil)
  end

  @impl Models.Argument
  @spec parse_argument(any(), any()) :: Models.Argument.Tuple.t()
  def parse_argument(arguments_ast, _) do
    tuple_arguments =
      arguments_ast
      |> Enum.map(fn argument_ast -> Models.Argument.parse_argument(argument_ast)
      end)

    argument = %Models.Argument.Tuple{
      arguments: tuple_arguments
    }

    argument
  end
end
