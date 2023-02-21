defmodule Verifier.Expressions.MapPut do
  alias Common.Indent, as: Indent

  def convert(new_map_variable, old_map_variable, key, value, indent_lvl) do
    converted_key = convert_key(key)
    converted_value = Verifier.Helpers.map_type(value)

    code =
      "#{Indent.build(indent_lvl)}#{new_map_variable} = Map.put(#{old_map_variable}, #{converted_key}, #{converted_value})"

    code
  end

  defp convert_key(key) do
    parts =
      String.split(key, "][")
      |> Enum.map(fn p -> p |> String.replace("[", "") |> String.replace("]", "") end)

    cond do
      length(parts) == 1 ->
        Verifier.Helpers.map_type(Enum.at(parts, 0))

      length(parts) > 1 ->
        mapped_parts =
          parts
          |> Enum.map(fn p -> Verifier.Helpers.map_type(p) end)

        "{#{Enum.join(mapped_parts, ", ")}}"
    end
  end
end
