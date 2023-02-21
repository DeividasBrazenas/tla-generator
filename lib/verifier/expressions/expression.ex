defmodule Verifier.Expressions.Expression do
  def convert(lines, variables_lines, indent_lvl) do
    {code_lines, conditions, _, _} =
      lines
      |> Enum.reduce({[], %{}, 0, 0}, fn _, {code_lines, conditions, curr_idx, next_idx} ->
        if curr_idx < next_idx do
          {code_lines, conditions, curr_idx + 1, next_idx}
        else
          {new_code_lines, new_conditions, new_next_idx} =
            convert_block(curr_idx, lines, conditions, variables_lines, indent_lvl)

          {code_lines ++ (new_code_lines |> List.flatten()),
           Map.merge(conditions, new_conditions), curr_idx + 1, new_next_idx}
        end
      end)

    {code_lines, conditions}
  end

  def convert_block(idx, lines, _, _, _) when length(lines) == idx do
    {[], %{}, idx + 1}
  end

  def convert_block(idx, lines, conditions, variables_lines, indent_lvl) do
    line = Enum.at(lines, idx)

    result =
      cond do
        (map_update_regex = Regex.run(~r/^ *(.*)\.(.*) := (.*);$/, line)) != nil ->
          variable = Enum.at(map_update_regex, 1)
          property = Enum.at(map_update_regex, 2)
          value = Enum.at(map_update_regex, 3)

          {[Verifier.Expressions.MapUpdate.convert([{variable, property, value}], indent_lvl)],
           %{}, idx + 1}

        (_map_update_multiple_regex = Regex.run(~r/^ *(.*)\.(.*) := (.*)$/, line)) != nil ->
          last_update_idx =
            idx + Verifier.Helpers.get_end_idx(Enum.slice(lines, idx..-1), ~r/^ *(.*) := (.*);$/)

          updates =
            Enum.slice(lines, idx..last_update_idx)
            |> Enum.map(fn l ->
              map_update_regex = Regex.run(~r/^ *\|?\|? (.*)\.(.*) := (.*);?$/, l)
              variable = Enum.at(map_update_regex, 1)
              property = Enum.at(map_update_regex, 2)
              value = String.replace(Enum.at(map_update_regex, 3), ";", "")
              {variable, property, value}
            end)

          {[Verifier.Expressions.MapUpdate.convert(updates, indent_lvl)], %{},
           last_update_idx + 1}

        (map_put_regex = Regex.run(~r/^ *(.*?)(\[.*\]) := (.*);$/, line)) != nil ->
          variable = Enum.at(map_put_regex, 1)
          key = Enum.at(map_put_regex, 2)
          value = Enum.at(map_put_regex, 3)

          {[Verifier.Expressions.MapPut.convert(variable, variable, key, value, indent_lvl)], %{},
           idx + 1}

        (enum_into_regex =
           Regex.run(
             ~r/^ *(.*) := \[(.*) \\in ([^ ]+) \|\-> (.*)];$/,
             line
           )) != nil ->
          variable = Enum.at(enum_into_regex, 1)
          iterator = Enum.at(enum_into_regex, 2)
          enumerable = Enum.at(enum_into_regex, 3)
          action = Enum.at(enum_into_regex, 4)

          {[
             Verifier.Expressions.EnumInto.convert(
               variable,
               enumerable,
               iterator,
               action,
               indent_lvl
             )
           ], %{}, idx + 1}

        (cond_regex =
           Regex.run(
             ~r/^ *(.*) := CASE$/,
             line
           )) != nil ->
          variable = Enum.at(cond_regex, 1)

          last_line_idx =
            idx +
              Verifier.Helpers.get_end_idx(Enum.slice(lines, idx..-1), ~r/^ *\[\] OTHER -> .*;$/)

          cond_lines = Enum.slice(lines, (idx + 1)..last_line_idx)

          {[
             Verifier.Expressions.Cond.convert(
               variable,
               cond_lines,
               indent_lvl
             )
           ], %{}, last_line_idx + 1}

        (if_regex = Regex.run(~r/^ *if (.*) then$/, line)) != nil ->
          condition = Verifier.Helpers.build_condition(Enum.at(if_regex, 1))

          last_line_idx =
            idx + Verifier.Helpers.get_end_idx(Enum.slice(lines, idx..-1), ~r/^ *end if;.*$/)

          line_after_if = Enum.at(lines, last_line_idx + 1)

          cond do
            line_after_if != nil and Regex.run(~r/^.*pin.*$/, line_after_if) != nil ->
              {[
                 Verifier.Expressions.Pin.convert(condition, indent_lvl)
               ], %{}, last_line_idx + 1}

            line_after_if != nil and Regex.run(~r/^.*condition.*$/, line_after_if) != nil ->
              {{left, nil, nil}, "/=", {right, nil, nil}} = condition
              regex = Regex.run(~r/^(.*)\[(\d+)\]$/, left)
              variable = Enum.at(regex, 1)
              {idx, _} = Integer.parse(Enum.at(regex, 2))
              current_conditions = Map.get(conditions, variable, [])
              conditions = Map.put(%{}, variable, current_conditions ++ [{idx - 1, right}])

              {[], conditions, last_line_idx + 1}

            true ->
              body = Enum.slice(lines, (idx + 1)..(last_line_idx - 1))
              else_idx = Enum.find_index(body, fn line -> Regex.run(~r/ *else */, line) end)

              if else_idx != nil do
                body = Enum.slice(lines, (idx + 1)..(idx + else_idx))
                else_body = Enum.slice(lines, (idx + else_idx + 2)..(last_line_idx - 1))

                {[
                   Verifier.Expressions.IfStatement.convert(
                     condition,
                     body,
                     else_body,
                     variables_lines,
                     indent_lvl
                   )
                 ], %{}, last_line_idx + 1}
              else
                {[
                   Verifier.Expressions.IfStatement.convert(
                     condition,
                     body,
                     [],
                     variables_lines,
                     indent_lvl
                   )
                 ], %{}, last_line_idx + 1}
              end
          end

        (return_regex = Regex.run(~r/^ *result := (.*);$/, line)) != nil ->
          return = Enum.at(return_regex, 1)
          {[Verifier.Expressions.Return.convert(return, indent_lvl)], %{}, idx + 1}

        (map_get_regex = Regex.run(~r/^ *(.*) := (.*)\[(.*)\];$/, line)) != nil ->
          variable = Enum.at(map_get_regex, 1)
          map_variable = Enum.at(map_get_regex, 2)
          key = Enum.at(map_get_regex, 3)

          {[Verifier.Expressions.MapGet.convert(variable, map_variable, key, indent_lvl)], %{},
           idx + 1}

        (assignment_regex = Regex.run(~r/^ *(.*) := (.*);$/, line)) != nil ->
          left = Enum.at(assignment_regex, 1)
          right = Enum.at(assignment_regex, 2)

          next_line = Enum.at(lines, idx + 1)

          cond do
            left == right ->
              {[
                 Verifier.Expressions.DefaultValueAssignment.convert(
                   left,
                   variables_lines,
                   indent_lvl
                 )
               ], %{}, idx + 1}

            Regex.run(~r/^ *map_put_\d+:$/, next_line) != nil ->
              map_put_regex = Regex.run(~r/^ *(.*?)(\[.*\]) := (.*);$/, Enum.at(lines, idx + 2))
              variable = Enum.at(map_put_regex, 1)
              key = Enum.at(map_put_regex, 2)
              value = Enum.at(map_put_regex, 3)

              {[Verifier.Expressions.MapPut.convert(variable, right, key, value, indent_lvl)],
               %{}, idx + 3}

            true ->
              {[
                 Verifier.Expressions.Assignment.convert(
                   left,
                   right,
                   indent_lvl
                 )
               ], %{}, idx + 1}
          end

        (_empty_line_regex = Regex.run(~r/^\s*$/, line)) != nil ->
          {[""], %{}, idx + 1}

        (_label_regex = Regex.run(~r/^.*:$/, line)) != nil ->
          {[], %{}, idx + 1}

        true ->
          {["not translated"], %{}, idx + 1}
      end

    result
  end
end
