defmodule Generators.Common.Constant do
  @spec to_tla_constant(any()) :: String.t()
  def to_tla_constant(value) do
    IO.inspect(value)

    cond do
      value == nil ->
        "NULL"

      is_boolean(value) ->
        case value do
          true -> "TRUE"
          false -> "FALSE"
        end

      is_number(value) ->
        to_string(value)

      true ->
        "\"#{Atom.to_string(value)}\""
    end
  end
end
