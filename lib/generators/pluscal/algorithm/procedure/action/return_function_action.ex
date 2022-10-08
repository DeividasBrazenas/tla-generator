defmodule Generators.PlusCal.Algorithm.Procedure.Action.Return.Function do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Algorithm.Procedure.Action

  @impl Generators.PlusCal.Algorithm.Procedure.Action
  @spec generate_action(any(), Integer.t()) :: List[String.t()]
  def generate_action(%Models.Action.Return.Function{} = action, indent_level) do
    [
      "#{Indent.build(indent_level)}call #{action.function_call}"
    ]
  end
end
