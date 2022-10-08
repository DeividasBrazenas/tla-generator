defmodule Models.Action.If do
  @moduledoc """
  Defines `if` action
  """
  @behaviour Models.Action

  use TypedStruct

  typedstruct do
    field(:condition, Models.Common.Condition.t(), default: nil, enforce: true)
    field(:actions, Models.Action.t(), default: [], enforce: true)
  end

  @impl Models.Action
  @spec parse_action(any) :: any() # Should be Models.Action.If.t()
  def parse_action(_ast) do
    action = %Models.Action.If{
      condition: nil,
      actions: []
    }
    action
  end
end
