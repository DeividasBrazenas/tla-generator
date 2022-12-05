defmodule Generators.PlusCal.Algorithm.Procedure.Expression.Call.Function do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Algorithm.Procedure.Expression

  @impl Generators.PlusCal.Algorithm.Procedure.Expression
  @spec generate_expression(any(), List[Models.Argument.t()], Integer.t()) :: List[String.t()]
  def generate_expression(%Models.Expression.Call.Function{} = _expression, _fn_inputs, _indent_level) do
    [""]
  end
end
