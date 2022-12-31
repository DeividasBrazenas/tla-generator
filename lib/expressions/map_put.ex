defmodule Expressions.MapPut do
  alias Common.Indent, as: Indent
  @expression :map_put

  @spec parse(atom(), atom(), any(), any(), Map.t(), Integer.t()) :: Expression.t()
  def parse(new_map_variable, old_map_variable, key, value, expressions_counter, indent_lvl) do
    counter = Map.get(expressions_counter, @expression, 0)

    assignment_lines =
      if new_map_variable != old_map_variable do
        ["#{Indent.build(indent_lvl)}#{Atom.to_string(new_map_variable)} := #{Atom.to_string(old_map_variable)};"] ++
        ["#{Indent.build(indent_lvl)}#{Atom.to_string(@expression)}_#{counter}:"]
      else
        []
      end

    parsed_key = parse_key(key, expressions_counter, indent_lvl)
    parsed_value = parse_value(value, expressions_counter, indent_lvl)

    lines = [
      "#{Indent.build(indent_lvl)}#{Atom.to_string(new_map_variable)}#{parsed_key} := #{parsed_value};"
    ]

    expression = %Expression{name: @expression}

    if assignment_lines != [] do
      %Expression{
        expression
        | lines: assignment_lines ++ lines,
          variables: [Atom.to_string(new_map_variable)],
          labels_count: 1
      }
    else
      %Expression{expression | lines: lines}
    end
  end

  @spec parse_key(any(), Map.t(), Integer.t()) :: String.t()
  def parse_key({_key_variable, _, nil} = key, expressions_counter, indent_lvl) do
    expression =
      Generator.Expressions.generate_expression(
        key,
        expressions_counter,
        %{},
        indent_lvl
      )

    %Expression{lines: lines} = expression

    "[#{Enum.at(lines, 0)}]"
  end

  def parse_key(key, expressions_counter, indent_lvl) do
    accessors =
      Tuple.to_list(key)
      |> Enum.map(fn k ->
        expression =
          Generator.Expressions.generate_expression(
            k,
            expressions_counter,
            %{},
            indent_lvl
          )

        %Expression{lines: lines} = expression

        "[#{Enum.at(lines, 0)}]"
      end)

    Enum.join(accessors, "")
  end

  @spec parse_value(any(), Map.t(), Integer.t()) :: String.t()
  def parse_value(value, expressions_counter, indent_lvl) do
    expression =
      Generator.Expressions.generate_expression(
        value,
        expressions_counter,
        %{},
        indent_lvl
      )

    %Expression{lines: lines} = expression

    Enum.at(lines, 0)
  end
end
