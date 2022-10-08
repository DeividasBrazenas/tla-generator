defmodule Generators.PlusCal.Algorithm.Procedure.Action.Return.Value do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Algorithm.Procedure.Action

  @impl Generators.PlusCal.Algorithm.Procedure.Action
  @spec generate_action(any(), Integer.t()) :: List[String.t()]
  def generate_action(%Models.Action.Return.Value{} = action, indent_level) do
    [
      "#{Indent.build(indent_level)}result_#{action.function_name} := #{action.value};",
      "#{Indent.build(indent_level)}return;"
    ]
  end
end
