defmodule Expressions.IfStatement do
  alias Common.Indent, as: Indent
  @expression :if_statement

  @spec parse(any(), any(), any(), Map.t(), Integer.t()) :: Expression.t()
  def parse(condition_ast, do_ast, else_ast, expressions_counter, indent_lvl) do
    counter = Map.get(expressions_counter, @expression, 0)

    condition = parse_condition(condition_ast)

    {do_block_lines, do_block_variables, do_block_definitions, _} =
      parse_actions(do_ast, indent_lvl + 2)

    {else_block_lines, else_block_variables, else_block_definitions, _} =
      parse_actions(else_ast, indent_lvl + 2)

    lines =
      ["#{Indent.build(indent_lvl)}if #{condition} then"] ++
        ["#{Indent.build(indent_lvl + 1)}if_#{counter}:"] ++
        do_block_lines ++
        ["#{Indent.build(indent_lvl)}else"] ++
        ["#{Indent.build(indent_lvl + 1)}else_#{counter}:"] ++
        else_block_lines ++
        ["#{Indent.build(indent_lvl)}end if;"]

    %Expression{
      name: @expression,
      lines: lines,
      variables: do_block_variables ++ else_block_variables,
      definitions: do_block_definitions ++ else_block_definitions
    }
  end

  @spec parse_actions(any(), Integer.t()) ::
          {List[String.t()], List[String.t()], List[String.t()], List[String.t()]}
  def parse_actions(body_ast, indent_lvl) when is_list(body_ast) do
    Generator.Expressions.generate_expressions(body_ast, indent_lvl)
  end

  def parse_actions(body_ast, indent_lvl) do
    Generator.Expressions.generate_expressions([body_ast], indent_lvl)
  end

  @spec parse_condition(any()) :: String.t()
  defp parse_condition(condition_ast) when is_list(condition_ast) do
    conditions = condition_ast |> Enum.map(fn condition_ast -> parse_condition(condition_ast) end)
    Enum.join(conditions, " ")
  end

  defp parse_condition(condition_ast) do
    expression = Generator.Expressions.generate_expression(condition_ast, %{}, %{}, 0)

    %Expression{lines: lines} = expression

    Enum.at(lines, 0)
  end
end
