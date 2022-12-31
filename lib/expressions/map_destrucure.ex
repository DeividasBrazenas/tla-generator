defmodule Expressions.MapDestrucure do
  alias Common.Indent, as: Indent
  @expression :map_destructure

  @spec parse(Map.t(), atom(), Integer.t()) :: Expression.t()
  def parse(assignments, src_variable, indent_lvl) do
    {lines, variables} =
      assignments
      |> Enum.reduce({[], []}, fn {key, assigned_value}, {lines_acc, variables_acc} ->
        {src_prop, _, nil} = assigned_value
        line = "#{Indent.build(indent_lvl)}#{Atom.to_string(key)} := #{src_variable}.#{src_prop};"
        {lines_acc ++ [line], variables_acc ++ [Atom.to_string(key)]}
      end)

    %Expression{name: @expression, lines: lines, variables: variables}
  end
end
