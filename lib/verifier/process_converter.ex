defmodule Verifier.ProcessConverter do
  alias Common.Indent, as: Indent

  def convert_process(process_lines, function_name, indent_lvl) do
    process_properties =
      process_lines
      |> Enum.with_index()
      |> Enum.reduce(%{}, fn {line, idx}, acc ->
        is_idx_inside_part =
          Map.values(acc)
          |> Enum.any?(fn {from_idx, to_idx, _} -> idx >= from_idx and idx <= to_idx end)

        if !is_idx_inside_part do
          {key, from_idx, to_idx, part_lines} =
            cond do
              (_process_declaration_regex = Regex.run(~r/^ *fair process.*$/, line)) != nil ->
                {nil, nil, nil, []}

              (_variables_regex = Regex.run(~r/^variables$/, line)) != nil ->
                variables_start_idx = idx + 1

                variables_end_idx =
                  idx +
                    Verifier.Helpers.get_end_idx(
                      Enum.slice(process_lines, variables_start_idx..-1),
                      nil
                    )

                variable_lines = Enum.slice(process_lines, variables_start_idx..variables_end_idx)

                {:input_variable_lines, variables_start_idx, variables_end_idx, variable_lines}

              (_body_regex = Regex.run(~r/^ *begin *$/, line)) != nil ->
                # Skip label
                body_start_idx = idx + 2

                body_end_idx =
                  idx +
                    Verifier.Helpers.get_end_idx(
                      Enum.slice(process_lines, body_start_idx..-1),
                      ~r/^ *end process.*$/
                    )

                body_lines = Enum.slice(process_lines, body_start_idx..body_end_idx)

                {:body_lines, body_start_idx, body_end_idx, body_lines}

              true ->
                {nil, nil, nil, ["not translated"]}
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

    {body, conditions} =
      Verifier.Expressions.Expression.convert(
        Map.get(process_properties, :body_lines, []),
        Map.get(process_properties, :input_variable_lines, []),
        indent_lvl + 1
      )

    input_variables =
      Verifier.VariablesConverter.convert(Map.get(process_properties, :input_variable_lines, []), conditions)

    process =
      ["#{Indent.build(indent_lvl)}def #{function_name}(#{Enum.join(input_variables, ", ")}) do"] ++
        body ++
        ["#{Indent.build(indent_lvl)}end"]

    process
  end
end
