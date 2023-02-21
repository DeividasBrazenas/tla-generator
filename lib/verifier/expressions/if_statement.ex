defmodule Verifier.Expressions.IfStatement do
  alias Common.Indent, as: Indent

  def convert(condition, body, else_body, variables_lines, indent_lvl) do
    {if_body_code, _} =
      Verifier.Expressions.Expression.convert(body, variables_lines, indent_lvl + 1)

    {else_body, _} =
      Verifier.Expressions.Expression.convert(else_body, variables_lines, indent_lvl + 1)

    code =
      ["#{Indent.build(indent_lvl)}if #{Verifier.Helpers.stringify_condition(condition)} do"] ++
        if_body_code

    if length(else_body) > 0 do
      code ++
        ["#{Indent.build(indent_lvl)}else"] ++
        else_body ++
        ["#{Indent.build(indent_lvl)}end"]
    else
      code ++ ["#{Indent.build(indent_lvl)}end"]
    end
  end
end
