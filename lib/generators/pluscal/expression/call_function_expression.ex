defmodule Generators.PlusCal.Expression.Call.Function do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Expression

  @impl Generators.PlusCal.Expression
  @spec generate_expression(any(), List[Models.Argument.t()], Integer.t()) :: List[String.t()]
  def generate_expression(%Models.Expression.Call.Function{} = _expression, _fn_inputs, _indent_level) do
    [""]
  end
end
