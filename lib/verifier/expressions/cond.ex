defmodule Verifier.Expressions.Cond do
  alias Common.Indent, as: Indent

  def convert(variable, condition_lines, indent_lvl) do
    conditions =
      condition_lines |> Enum.map(fn line -> convert_condition(line, indent_lvl + 2) end)

    code =
      ["#{Indent.build(indent_lvl)}#{variable} ="] ++
        ["#{Indent.build(indent_lvl + 1)}cond do"] ++
        conditions ++
        ["#{Indent.build(indent_lvl + 1)}end"]

    code
  end

  defp convert_condition(line, indent_lvl) do
    cond do
      (standard_condition_regex = Regex.run(~r/^ *\[\] OTHER -> (.*);$/, line)) != nil ->
        action = Verifier.Helpers.map_type(Enum.at(standard_condition_regex, 1))

        "#{Indent.build(indent_lvl)}true -> #{action}"

      (standard_condition_regex = Regex.run(~r/^(.*) -> (.*)$/, line)) != nil ->
        condition = Verifier.Helpers.build_condition(Enum.at(standard_condition_regex, 1))
        action = Verifier.Helpers.map_type(Enum.at(standard_condition_regex, 2))

        "#{Indent.build(indent_lvl)}#{Verifier.Helpers.stringify_condition(condition)} -> #{action}"
    end
  end
end
