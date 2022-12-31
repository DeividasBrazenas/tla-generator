defmodule Expressions.MapUpdate do
  alias Common.Indent, as: Indent
  @expression :map_update
  @spec parse(atom(), atom(), Map.t(), Map.t(), Integer.t()) :: Expression.t()
  def parse(variable, src_variable, updates, expressions_counter, indent_lvl) do
    assignment_line =
      if variable != src_variable do
        "#{Indent.build(indent_lvl)}#{Atom.to_string(variable)} := #{Atom.to_string(src_variable)};"
      else
        nil
      end

    keys = Map.keys(updates)

    first_key = Enum.at(keys, 0)
    first_value = parse_value(updates[first_key], expressions_counter, indent_lvl)

    first_line =
      "#{Indent.build(indent_lvl)}#{Atom.to_string(variable)}.#{first_key} := #{first_value}"

    upd_lines =
      case Enum.count(keys) do
        1 ->
          ["#{first_line};"]

        _ ->
          lines =
            Enum.map(Enum.slice(keys, 1..-2), fn key ->
              value = parse_value(updates[key], expressions_counter, indent_lvl)
              "#{Indent.build(indent_lvl)}|| #{Atom.to_string(variable)}.#{key} := #{value}"
            end)

          last_key = List.last(keys)
          last_value = parse_value(updates[last_key], expressions_counter, indent_lvl)

          last_line =
            "#{Indent.build(indent_lvl)}|| #{Atom.to_string(variable)}.#{last_key} := #{last_value};"

          [first_line] ++ lines ++ [last_line]
      end

    expression = %Expression{name: @expression}

    if assignment_line != nil do
      %Expression{
        expression
        | lines: [assignment_line] ++ upd_lines,
          variables: [Atom.to_string(variable)]
      }
    else
      %Expression{expression | lines: upd_lines}
    end
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
