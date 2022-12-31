defmodule Expressions.Boolean do
  @spec parse(boolean()) :: Expression.t()
  def parse(arg) when is_boolean(arg) do
    expression = %Expression{name: :boolean}

    case arg do
      true -> %Expression{expression | lines: ["TRUE"]}
      false -> %Expression{expression | lines: ["FALSE"]}
    end
  end
end
