defmodule Verifier.Expressions.Assignment do
  alias Common.Indent, as: Indent

  def convert(left, right, indent_lvl) do
    code =
      "#{Indent.build(indent_lvl)}#{Verifier.Helpers.map_type(left)} = #{Verifier.Helpers.map_type(right)}"

    code
  end
end
