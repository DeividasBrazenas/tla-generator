defmodule Generators.PlusCal.Expression.Call.ExternalFunction do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Expression

  @impl Generators.PlusCal.Expression
  @spec generate_expression(any(), List[Models.Type.t()], List[atom()], Integer.t()) :: List[String.t()]
  def generate_expression(%Models.Expression.Call.ExternalFunction{} = _expression, _fn_inputs, _local_variables, _indent_level) do
    [""]
  end
end
