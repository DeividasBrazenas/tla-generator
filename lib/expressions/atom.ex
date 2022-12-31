defmodule Expressions.Atom do
  @spec parse(atom()) :: Expression.t()
  def parse(arg) when is_atom(arg) do
    %Expression{name: :atom, lines: ["\"#{Atom.to_string(arg)}\""]}
  end
end
