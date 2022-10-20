defmodule Models.Function.Clause.Metadata do
  @moduledoc """
  Module defining the function's metadata
  """
  use TypedStruct

  typedstruct do
    field(:name, atom(), default: nil, enforce: true)
    field(:arguments, List[Models.Argument.t()], default: [])
    field(:condition, Models.Common.Condition.t(), default: nil)
  end

  @doc """
  Parses the metadata of function's clause
  """
  @spec parse_metadata(any()) :: Models.Function.Clause.Metadata.t()
  def parse_metadata({:when, _, [{name, _, arguments_ast}, condition_ast]}) do
    arguments =
      arguments_ast
      |> Enum.map(fn argument_ast -> Models.Argument.parse_argument(argument_ast) end)

    metadata = %Models.Function.Clause.Metadata{
      name: name,
      arguments: arguments,
      condition: Models.Common.Condition.parse_condition(condition_ast)
    }

    metadata
  end

  def parse_metadata({name, _, arguments_ast}) do
    arguments =
      arguments_ast
      |> Enum.map(fn argument_ast -> Models.Argument.parse_argument(argument_ast) end)

    metadata = %Models.Function.Clause.Metadata{
      name: name,
      arguments: arguments,
      condition: nil
    }

    metadata
  end
end
