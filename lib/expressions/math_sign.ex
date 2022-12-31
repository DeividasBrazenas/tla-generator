defmodule Expressions.MathSign do
  @expression :math_sign

  @spec parse(any(), any(), atom()) :: Expression.t()
  def parse(left_ast, right_ast, sign) do
    left_expression =
      Generator.Expressions.generate_expression(left_ast, %{}, %{}, 0)

    %Expression{lines: left_lines} = left_expression
    left = Enum.at(left_lines, 0)

    right_expression =
      Generator.Expressions.generate_expression(right_ast, %{}, %{}, 0)

    %Expression{lines: right_lines} = right_expression
    right = Enum.at(right_lines, 0)

    line = "(#{left} #{get_sign(sign)} #{right})"

    expression = %Expression{name: @expression, lines: [line]}
    expression
  end

  @spec get_sign(atom()) :: String.t()
  defp get_sign(sign) do
    case sign do
      :== -> "="
      :< -> "<"
      :> -> ">"
      :<= -> "<="
      :>= -> ">="
      :+ -> "+"
      :- -> "-"
      :* -> "*"
      :/ -> "\\div"
      :and -> "/\\"
      :or -> "\\/"
    end
  end
end
