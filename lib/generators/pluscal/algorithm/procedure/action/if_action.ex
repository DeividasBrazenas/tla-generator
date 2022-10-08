defmodule Generators.PlusCal.Algorithm.Procedure.Action.If do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Algorithm.Procedure.Action

  @impl Generators.PlusCal.Algorithm.Procedure.Action
  @spec generate_action(any(), Integer.t()) :: List[String.t()]
  def generate_action(%Models.Action.If{} = action, indent_level) do
    action =
      [
        "#{Indent.build(indent_level)}if #{Generators.Common.Condition.generate_condition(action.condition)} then"
      ] ++
        generate_condition_satisfied_actions(action.condition_satisfied_actions, indent_level + 1) ++
        generate_condition_unsatisfied_actions(
          action.condition_unsatisfied_actions,
          indent_level + 1
        ) ++
        [
          "#{Indent.build(indent_level)}end if;"
        ]

    action
  end

  @spec generate_condition_satisfied_actions(List[Models.Action.t()], Integer.t()) ::
          List[String.t()]
  defp generate_condition_satisfied_actions(actions, indent_level) do
    Generators.PlusCal.Algorithm.Procedure.Action.generate_actions(actions, indent_level)
  end

  @spec generate_condition_unsatisfied_actions(List[Models.Action.t()], Integer.t()) ::
          List[String.t()]
  defp generate_condition_unsatisfied_actions(actions, indent_level) do
    if length(actions) > 0 do
      ["#{Indent.build(indent_level - 1)}else"] ++
        Generators.PlusCal.Algorithm.Procedure.Action.generate_actions(actions, indent_level)
    else
      []
    end
  end
end
