defmodule Verifier.Helpers do
  def map_type(arg) do
    cond do
      is_list(arg) ->
        tuple_elements = arg |> Enum.map(fn e -> map_type(e) end)
        "{#{Enum.join(tuple_elements, ", ")}}"

      arg == "TRUE" ->
        true

      arg == "FALSE" ->
        false

      arg == "NULL" ->
        "nil"

      tuple_regex = Regex.run(~r/^<<(.*)>>$/, arg) ->
        tuple_elements = Enum.at(tuple_regex, 1)

        tuple_content =
          String.split(tuple_elements, ",")
          |> Enum.map(fn e -> map_type(String.trim(e)) end)
          |> Enum.join(", ")

        "{#{tuple_content}}"

      atom_regex = Regex.run(~r/^"(.*)"$/, arg) ->
        atom_string = Enum.at(atom_regex, 1)
        ":#{atom_string}"

      true ->
        arg
    end
  end

  def get_end_idx(lines, nil) do
    idx =
      Enum.find_index(lines, fn line ->
        Regex.run(~r/^ *variables$/, line) != nil or
          Regex.run(~r/^ *define$/, line) != nil or
          Regex.run(~r/^ *fair process.*$/, line) != nil or
          Regex.run(~r/^ *begin.*$/, line) != nil
      end)

    case idx do
      nil -> length(lines)
      _ -> idx
    end
  end

  def get_end_idx(lines, expected_regex) do
    idx =
      Enum.find_index(lines, fn line ->
        Regex.run(expected_regex, line) != nil
      end)

    case idx do
      nil -> length(lines)
      _ -> idx
    end
  end

  def build_condition(condition) do
    cond do
      (condition_regex = Regex.run(~r/^\(([^\(\)]+) (.*) ([^\(\)]+)\)$/, condition)) != nil ->
        left = Enum.at(condition_regex, 1)
        sign = Enum.at(condition_regex, 2)
        right = Enum.at(condition_regex, 3)

        {build_condition(left), sign, build_condition(right)}

      (negation_regex = Regex.run(~r/^~(.*)$/, condition)) != nil ->
        {"not", nil, build_condition(Enum.at(negation_regex, 1))}

      !String.contains?(condition, "/\\") and
        !String.contains?(condition, "\\/") and
        !String.contains?(condition, "+") and
        !String.contains?(condition, "-") and
        !String.contains?(condition, "*") and
          !String.contains?(condition, "\\div") ->
        {condition, nil, nil}

      (condition_regex = Regex.run(~r/\(([^()]|(?R))*\)/, condition)) != nil ->
        right = Enum.at(condition_regex, 1)

        left_regex =
          Regex.run(
            ~r/^(.*) (.*)$/,
            String.slice(Enum.at(condition_regex, 0), 1..-2)
            |> String.replace_trailing(right, "")
            |> String.trim()
          )

        last_element = List.last(left_regex)

        case String.ends_with?(last_element, "_fn") do
          true ->
            right = "#{last_element}#{right}"

            sign_regex = Regex.run(~r/^.* (.*)$/, Enum.at(left_regex, 1))
            sign = Enum.at(sign_regex, 1)
            left = String.replace_trailing(Enum.at(left_regex, 1), sign, "") |> String.trim()

            {build_condition(left), sign, build_condition(right)}

          false ->
            left = Enum.at(left_regex, 1)
            sign = Enum.at(left_regex, 2)

            {build_condition(left), sign, build_condition(right)}
        end

      true ->
        {condition, nil, nil}
    end
  end

  def stringify_condition({left, nil, nil}) do
    cond do
      (anon_fn_regex = Regex.run(~r/(.*)_fn\((.*)\)/, left)) != nil ->
        name = Enum.at(anon_fn_regex, 1)
        args = map_type(Enum.at(anon_fn_regex, 2))
        "#{name}.(#{args})"

      true ->
        map_type(left)
    end
  end

  def stringify_condition({"not", nil, right}) do
    "not #{stringify_condition(right)}"
  end

  def stringify_condition({left, sign, right}) do
    stringified_left = stringify_condition(left)
    stringified_sign = parse_sign(sign)
    stringified_right = stringify_condition(right)

    "(#{stringified_left} #{stringified_sign} #{stringified_right})"
  end

  def parse_sign(sign) do
    case sign do
      "/\\" -> "and"
      "\\/" -> "or"
      "\\div" -> "/"
      "=" -> "=="
      _ -> sign
    end
  end
end
