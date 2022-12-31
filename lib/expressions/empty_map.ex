defmodule Expressions.EmptyMap do
  @expression :empty_map

  @spec parse() :: Expression.t()
  def parse() do
    # Might be not correct, but TLA+ doesn't have a way to define empty structure
    line = "{}"
    %Expression{name: @expression, lines: [line]}
  end
end
