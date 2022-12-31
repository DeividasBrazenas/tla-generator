defmodule Expressions.EnumInto do
  alias Common.Indent, as: Indent
  @expression :enum_into

  #  msgs := [p \in peers |-> msgs[p] \cup {<<"PROPOSE", me, input>>}];
  # msgs = Enum.into(peers, %{}, fn peer_id -> {peer_id, [{:PROPOSE, me, input}]} end)

  @spec parse(atom(), atom(), any(), any(), Integer.t()) :: Expression.t()
  def parse(variable, enumerable, {iterator, _, nil}, action_ast, indent_lvl) do
    action = parse_action(variable, action_ast)

    line =
      "#{Indent.build(indent_lvl)}#{variable} := [#{iterator} \\in #{enumerable} |-> #{action}];"

    %Expression{name: @expression, lines: [line], variables: [Atom.to_string(variable)]}
  end

  # @spec parse(atom(), atom(), any(), any(), Map.t(), Integer.t()) :: Expression.t()
  # def parse(variable, enumerable, {iterator, _, nil}, action, expressions_counter, indent_lvl) do
  #   counter = Map.get(expressions_counter, @expression, 0)

  #   index_var = "enum_into_#{counter}_idx"

  #   lines =
  #     ["#{Indent.build(indent_lvl)}enum_into_#{counter}:"] ++
  #       ["#{Indent.build(indent_lvl + 1)}while #{index_var} <= Len(#{enumerable}) do"] ++
  #       ["#{Indent.build(indent_lvl + 2)}#{iterator} := #{enumerable}[#{index_var}];"] ++
  #       [parse_action(variable, iterator, action, expressions_counter, indent_lvl + 2)] ++
  #       ["#{Indent.build(indent_lvl + 2)}#{index_var} := #{index_var} + 1;"] ++
  #       ["#{Indent.build(indent_lvl + 1)}end while;"]

  #   %Expression{name: @expression, lines: lines, variables: ["#{index_var} = 1", Atom.to_string(iterator)], labels_count: 1}
  # end

  @spec parse_action(atom(), any()) :: String.t()
  defp parse_action(variable, {{key, _, nil}, [value]}) do
    action_expression = Generator.Expressions.generate_expression(value, %{}, %{}, 0)

    %Expression{lines: action_lines} = action_expression
    action = Enum.at(action_lines, 0)

    "#{variable}[#{key}] \\cup {#{action}}"
  end
end
