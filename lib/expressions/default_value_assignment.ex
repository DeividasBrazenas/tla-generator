defmodule Expressions.DefaultValueAssignment do
  alias Common.Indent, as: Indent
  @expression :default_value_assignment

  @spec parse(atom(), Integer.t()) :: Expression.t()
  def parse(variable, indent_lvl) do
    # Assign variable to itself as it already should have a default value set in TLA+
    lines = ["#{Indent.build(indent_lvl)}#{variable} := #{variable};"]

    %Expression{name: @expression, lines: lines, variables: [Atom.to_string(variable)]}
  end
end
