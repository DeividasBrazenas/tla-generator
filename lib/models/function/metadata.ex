defmodule Models.Function.Case.Metadata do
  @moduledoc """
  Module defining the function's metadata
  """
  use TypedStruct

  typedstruct do
    field(:name, atom(), default: nil, enforce: true)
    field(:arguments, List[atom()], default: [])
    field(:condition, Models.Common.Condition.t(), default: nil)
  end

  @doc """
  Parses the metadata of function's case
  """
  @spec parse_metadata(any()) :: Models.Function.Case.Metadata.t()
  def parse_metadata({:when, _, [{name, _, arguments}, condition_ast]}) do
    metadata = %Models.Function.Case.Metadata{
      name: name,
      arguments: Enum.map(arguments, fn {argument, _, _} -> argument end),
      condition: Models.Common.Condition.parse_condition(condition_ast)
    }

    metadata
  end

  def parse_metadata({name, _, arguments}) do
    metadata = %Models.Function.Case.Metadata{
      name: name,
      arguments: Enum.map(arguments, fn {argument, _, _} -> argument end),
      condition: nil
    }

    metadata
  end
end
