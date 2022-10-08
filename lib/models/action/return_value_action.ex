defmodule Models.Action.Return.Value do
  @moduledoc """
  Defines `if` action
  """
  @behaviour Models.Action

  use TypedStruct

  typedstruct do
    field(:value, atom(), default: nil, enforce: true)
    field(:function_name, atom(), default: nil, enforce: true)
  end

  @impl Models.Action
  @spec parse_action(Models.Function.Case.Metadata.t(), any()) :: any()
  def parse_action(metadata, {value, _, nil}) do
    action = %Models.Action.Return.Value{
      value: value,
      function_name: metadata.name
    }

    action
  end
end
