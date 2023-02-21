defmodule Verifier.Expressions.Pin do
  alias Common.Indent, as: Indent

  def convert(condition, indent_lvl) do
    {{left, nil, nil}, "/=", {right, nil, nil}} = condition

    code =
      "#{Indent.build(indent_lvl)}^#{Verifier.Helpers.map_type(left)} = #{Verifier.Helpers.map_type(right)}"

    code
  end
end
