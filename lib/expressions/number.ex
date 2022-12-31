defmodule Expressions.Number do
  @spec parse(number()) :: Expression.t()
  def parse(arg) when is_number(arg) do
    %Expression{name: :number, lines: ["#{arg}"]}
  end
end
