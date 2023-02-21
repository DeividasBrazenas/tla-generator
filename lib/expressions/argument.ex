defmodule Expressions.Argument do
  @spec parse(List[any()]) :: List[String.t()]
  def parse(arguments_ast) do
    arguments =
      arguments_ast
      |> Enum.map(fn a -> parse_argument(a, "") end)
      |> List.flatten()
      |> Enum.filter(fn a -> a != nil end)

    arguments
  end

  defp parse_argument({:=, _, [{:{}, _, tuple_arguments}, {variable, _, nil}]}, _) do
    tuple_arguments
    |> Enum.with_index(fn a, idx -> parse_argument(a, "#{variable}[#{idx + 1}]") end)
  end

  defp parse_argument({variable, _, nil}, accessor) do
    case accessor != "" do
      false -> nil
      true -> "#{variable} = #{accessor}"
    end
  end

  defp parse_argument(_, _) do
    nil
  end
end
