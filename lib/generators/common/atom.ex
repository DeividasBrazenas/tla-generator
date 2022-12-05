defmodule Generators.Common.Constant do
  @spec to_tla_constant(any()) :: String.t()
  def to_tla_constant(constant) do
    cond do
      constant == :nil -> "NULL"
      is_boolean(constant) ->
        case constant do
          true -> "TRUE"
          false -> "FALSE"
        end

      true ->
        "\"#{Atom.to_string(constant)}\""
    end
  end
end
