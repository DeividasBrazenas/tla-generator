defmodule Expressions.Cond do
  alias Common.Indent, as: Indent
  @expression :cond

  @spec parse(atom(), any(), Integer.t()) :: Expression.t()
  def parse(variable, conditions_ast, indent_lvl) do
    conditions =
      conditions_ast |> Enum.map(fn condition_ast -> parse_condition(condition_ast) end)

    heading = "#{Indent.build(indent_lvl)}#{variable} := CASE"

    first_condition = "#{Indent.build(indent_lvl + 2)}#{List.first(conditions)}"

    middle_conditions =
      Enum.slice(conditions, 1..-2)
      |> Enum.map(fn condition -> "#{Indent.build(indent_lvl + 2)}[] #{condition};" end)

    last_condition = "#{Indent.build(indent_lvl + 2)}[] #{List.last(conditions)};"

    lines =
      [heading] ++
        [first_condition] ++
        middle_conditions ++
        [last_condition]

    %Expression{name: @expression, lines: lines, variables: [Atom.to_string(variable)]}
  end

  @spec parse_condition(any()) :: String.t()
  defp parse_condition({:->, _, [[true], action]}) do
    action_expression = Generator.Expressions.generate_expression(action, %{}, %{}, 0)
    %Expression{lines: action_lines} = action_expression
    action = Enum.at(action_lines, 0)
    "OTHER -> #{action}"
  end

  defp parse_condition({:->, _, [[condition], action]}) do
    condition_expression = Generator.Expressions.generate_expression(condition, %{}, %{}, 0)
    %Expression{lines: condition_lines} = condition_expression
    condition = Enum.at(condition_lines, 0)

    action_expression = Generator.Expressions.generate_expression(action, %{}, %{}, 0)
    %Expression{lines: action_lines} = action_expression
    action = Enum.at(action_lines, 0)
    "#{condition} -> #{action}"
  end

  # x := CASE index = 5 -> FALSE
  # [] OTHER -> TRUE;
end

# {:->, [line: 254], [[{:and, [line: 254], [{:>, [line: 254], [{:count, [line: 254], nil}, {:*, [line: 254], [3, {:f, [line: 254], nil}]}]}, {:==, [line: 254], [{:output, [line: 254], nil}, nil]}]}], {:value, [line: 254], nil}]}
