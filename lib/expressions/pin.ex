defmodule Expressions.Pin do
  alias Common.Indent, as: Indent
  @expression :pin

  @spec parse(atom(), any(), Map.t(), Integer.t()) :: Expression.t()
  def parse(left_operand, right_operand, expressions_counter, indent_lvl) do
    counter = Map.get(expressions_counter, :pin, 0)

    expression =
      Generator.Expressions.generate_expression(right_operand, expressions_counter, %{}, indent_lvl)

    %Expression{lines: lines} = expression

    lines =
      [
        "#{Indent.build(indent_lvl)}if #{left_operand} /= #{Enum.at(lines, 0)} then"
      ] ++
        ["#{Indent.build(indent_lvl + 1)}goto Done;"] ++
        ["#{Indent.build(indent_lvl)}end if;"] ++
        ["#{Indent.build(indent_lvl)}after_pin_#{counter}:"]

    %Expression{name: @expression, lines: lines, labels_count: 1}
  end
end
