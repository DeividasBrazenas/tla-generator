defmodule Generators.PlusCal.Algorithm.Procedure.Action do
  @callback generate_action(any(), Integer.t()) :: List[String.t()]

  @spec generate_actions(List[Models.Action.t()], Integer.t()) :: List[String.t()]
  def generate_actions(action_models, indent_level) do
    actions =
      action_models
      |> Enum.flat_map(fn action ->
        case action do
          %Models.Action.Return.Value{} -> Generators.PlusCal.Algorithm.Procedure.Action.Return.Value.generate_action(action, indent_level)
          %Models.Action.Return.Function{} -> Generators.PlusCal.Algorithm.Procedure.Action.Return.Function.generate_action(action, indent_level)
        end
      end)

    actions
  end
end
