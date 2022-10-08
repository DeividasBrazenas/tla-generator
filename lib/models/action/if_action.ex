defmodule Models.Action.If do
  @moduledoc """
  Defines `if` action
  """
  @behaviour Models.Action

  use TypedStruct

  typedstruct do
    field(:condition, Models.Common.Condition.t(), default: nil, enforce: true)
    field(:condition_satisfied_actions, List[Models.Action.t()], default: [])
    field(:condition_unsatisfied_actions, List[Models.Action.t()], default: [])
  end

  @impl Models.Action
  @spec parse_action(Models.Function.Case.Metadata.t(), any()) :: any()
  def parse_action(metadata, {:if, _, [condition, actions_ast]}) do
    {do_actions, else_actions} = get_inner_actions(metadata, actions_ast)

    action = %Models.Action.If{
      condition: Models.Common.Condition.parse_condition(condition),
      condition_satisfied_actions: do_actions,
      condition_unsatisfied_actions: else_actions
    }

    action
  end

  @spec get_inner_actions(Models.Function.Case.Metadata.t(), any()) ::
          {List[Models.Action.t()], List[Models.Action.t()]}
  defp get_inner_actions(metadata, [do_ast, else_ast]) do
    do_actions = Models.Action.parse_actions(metadata, [do_ast])
    else_actions = Models.Action.parse_actions(metadata, [else_ast])
    {do_actions, else_actions}
  end

  defp get_inner_actions(metadata, [do_ast]) do
    do_actions = Models.Action.parse_actions(metadata, [do_ast])
    {do_actions, []}
  end
end
