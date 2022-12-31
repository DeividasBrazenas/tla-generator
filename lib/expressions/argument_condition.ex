defmodule Expressions.ArgumentCondition do
  alias Common.Indent, as: Indent
  @expression :argument_condition

  @spec parse(List[any()], Integer.t()) :: List[String.t()]
  def parse(arguments_ast, indent_lvl) do
    conditions =
      arguments_ast
      |> Enum.flat_map(fn arg -> generate_condition(arg, "") end)

    result =
      case length(conditions) do
        0 ->
          []

        _ ->
          ["#{Indent.build(indent_lvl)}if #{Enum.join(conditions, " \\/ ")} then"] ++
            ["#{Indent.build(indent_lvl + 1)}goto Done;"] ++
            ["#{Indent.build(indent_lvl)}end if;"] ++
            ["#{Indent.build(indent_lvl)}after_condition:"] ++
            [""]
      end

    result
  end

  @spec generate_condition(any(), String.t()) :: List[String.t()]
  defp generate_condition({_, _, nil}, _prefix), do: []

  defp generate_condition(arg, prefix) when is_atom(arg),
    do: "#{prefix} /= \"#{Atom.to_string(arg)}\""

  defp generate_condition(arg, prefix) when is_binary(arg), do: "#{prefix} /= \"#{arg}\""

  defp generate_condition(arg, prefix) when is_number(arg), do: "#{prefix} /= #{arg}"

  defp generate_condition({:=, _, [{:{}, _, arguments_ast}, {variable, _, nil}]}, prefix) do
    arguments_ast
    |> Enum.with_index(fn arg, idx ->
      generate_condition(arg, "#{prefix}#{variable}[#{idx + 1}]")
    end)
    |> List.flatten()
  end
end
