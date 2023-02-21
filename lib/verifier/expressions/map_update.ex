defmodule Verifier.Expressions.MapUpdate do
  alias Common.Indent, as: Indent

  def convert(updates, indent_lvl) do
    code =
      updates
      |> Enum.group_by(fn {variable, _, _} -> variable end, fn {_, property, value} ->
        {property, value}
      end)
      |> Enum.map(fn {variable, values} ->
        values_code =
          values
          |> Enum.map(fn {property, value} ->
            "#{property}: #{Verifier.Helpers.map_type(value)}"
          end)

        "#{Indent.build(indent_lvl)}#{variable} = %{#{variable} | #{Enum.join(values_code, ", ")}}"
      end)

    code
  end
end
