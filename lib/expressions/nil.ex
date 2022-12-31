defmodule Expressions.Nil do
  @expression :nil
  def parse() do
    %Expression{name: @expression, lines: ["NULL"]}
  end
end
