defmodule Expressions.MapSize do
  alias Common.Indent, as: Indent
  @expression :map_size

  @spec parse(atom(), atom(), Integer.t()) :: Expression.t()
  def parse(variable, argument, indent_lvl) do
    line = "#{Indent.build(indent_lvl)}#{variable} := map_size(#{argument});"

    # As all keys are initialized, we count keys with non-null values
    definition =
      "map_size(structure) == Cardinality({k \\in (DOMAIN structure) : structure[k] /= NULL})"

    expression = %Expression{name: @expression, lines: [line], variables: [Atom.to_string(variable)], definitions: [definition]}
    expression
  end
end
