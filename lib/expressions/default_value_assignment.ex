defmodule Expressions.DefaultValueAssignment do
  @expression :default_value_assignment

  @spec parse(atom()) :: Expression.t()
  def parse(_variable) do
    # We do not do anything, as default value should already be assigned in TLA+ from config
    %Expression{name: @expression}
  end
end
