defmodule Verifier.VariablesConverter do
  def convert(variable_lines, conditions) do
    variables =
      variable_lines
      |> Enum.reduce([], fn line, acc ->
        cond do
          (input_variable_regex = Regex.run(~r/^ *(.*) = (.*)\[self\].*$/, line)) != nil ->
            variable = Enum.at(input_variable_regex, 1)
            acc ++ [variable]

          true ->
            acc
        end
      end)
      |> Enum.map(fn v ->
        destructions =
          variable_lines
          |> Enum.reduce([], fn vl, acc ->
            res = Regex.run(~r/^ *(.*) = #{v}\[(\d+)\],$/, vl)

            if res != nil do
              {var_idx, _} = Integer.parse(Enum.at(res, 2))
              acc ++ [{var_idx - 1, Enum.at(res, 1)}]
            else
              acc
            end
          end)

        destructions =
          (destructions ++ Map.get(conditions, v, []))
          |> Enum.sort(fn {idx1, _}, {idx2, _} -> idx1 <= idx2 end)
          |> Enum.map(fn {_idx, value} -> value end)

        if length(destructions) == 0 do
          v
        else
          "#{Verifier.Helpers.map_type(destructions)} = #{v}"
        end
      end)

    variables
  end
end
