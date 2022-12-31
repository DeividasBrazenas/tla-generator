defmodule Expressions.Variable do
  @spec parse(atom()) :: Expression.t()
  def parse(arg) do
    %Expression{name: :variable, lines: ["#{Atom.to_string(arg)}"]}
  end
end
