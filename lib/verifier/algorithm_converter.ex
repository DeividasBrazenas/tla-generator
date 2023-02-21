defmodule Verifier.AlgorithmConverter do
  def convert_algorithm(lines, function_name, indent_lvl) do
    algorithm_parts =
      lines
      |> Enum.with_index()
      |> Enum.reduce(%{}, fn {line, idx}, acc ->
        is_idx_inside_part =
          Map.values(acc)
          |> Enum.any?(fn {from_idx, to_idx, _} -> idx >= from_idx and idx <= to_idx end)

        if !is_idx_inside_part do
          {key, from_idx, to_idx, part_lines} =
            cond do
              (_variables_regex = Regex.run(~r/^variables$/, line)) != nil ->
                variables_start_idx = idx + 1

                variables_end_idx =
                  idx + Verifier.Helpers.get_end_idx(Enum.slice(lines, variables_start_idx..-1), nil)

                variables_lines = Enum.slice(lines, variables_start_idx..variables_end_idx)
                {:global_variables, variables_start_idx, variables_end_idx, variables_lines}

              (_define_regex = Regex.run(~r/^define$/, line)) != nil ->
                define_start_idx = idx + 1

                define_end_idx =
                  idx + Verifier.Helpers.get_end_idx(Enum.slice(lines, define_start_idx..-1), ~r/^ *end define.*$/)

                define_lines = Enum.slice(lines, define_start_idx..define_end_idx)
                {:definitions, define_start_idx, define_end_idx, define_lines}

              (_process_regex = Regex.run(~r/^ *fair process.*$/, line)) != nil ->
                process_start_idx = idx + 1

                process_end_idx =
                  idx +
                  Verifier.Helpers.get_end_idx(Enum.slice(lines, process_start_idx..-1), ~r/^ *end process.*$/)

                process_lines = Enum.slice(lines, process_start_idx..process_end_idx)
                process = Verifier.ProcessConverter.convert_process(process_lines, function_name, indent_lvl)
                {:process, process_start_idx, process_end_idx, process}

              true ->
                {nil, nil, nil, nil}
            end

          if key != nil do
            acc = Map.put(acc, key, {from_idx, to_idx, part_lines})
            acc
          else
            acc
          end
        else
          acc
        end
      end)
      |> Enum.reduce(%{}, fn {key, {_, _, lines}}, acc ->
        Map.put(acc, key, lines)
      end)

      Map.get(algorithm_parts, :process)
  end
end
