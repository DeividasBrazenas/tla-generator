defmodule Verifier.Expressions.Return do
  alias Common.Indent, as: Indent

  def convert(return, indent_lvl) do
    code = "#{Indent.build(indent_lvl)}#{Verifier.Helpers.map_type(return)}"

    code
  end
end
