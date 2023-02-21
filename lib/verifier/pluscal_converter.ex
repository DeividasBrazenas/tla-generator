defmodule Verifier.PluscalConverter do
  def convert_to_code(file_path, module_name, function_name) do
    lines =
      file_path
      |> File.read!()
      |> String.split("\r\n")

    # Drop generated TLA+
    begin_translation_index =
      Enum.find_index(lines, fn line ->
        Regex.run(~r/.*BEGIN TRANSLATION.*/, line) != nil
      end)

    lines = Enum.take(lines, begin_translation_index)

    properties =
      lines
      |> Enum.with_index()
      |> Enum.reduce(%{}, fn {line, idx}, acc ->
        cond do
          (_module_regex = Regex.run(~r/^\-* MODULE (.*?) \-*$/, line)) != nil ->
            # acc = Map.put(acc, :function_name, Enum.at(module_regex, 1))
            acc

          (_extends_regex = Regex.run(~r/^EXTENDS.*$/, line)) != nil ->
            acc

          (_constant_regex = Regex.run(~r/^CONSTANT.*$/, line)) != nil ->
            acc

          (_algorithm_regex = Regex.run(~r/^\(\*\-\-algorithm.*$$/, line)) != nil ->
            algorithm_begin_idx = idx + 1

            algorithm_end_idx =
              idx +
                Verifier.Helpers.get_end_idx(
                  Enum.slice(lines, algorithm_begin_idx..-1),
                  ~r/.*end algorithm;.*/
                )

            algorithm_lines = Enum.slice(lines, algorithm_begin_idx..algorithm_end_idx)

            algorithm =
              Verifier.AlgorithmConverter.convert_algorithm(algorithm_lines, function_name, 1)

            acc = Map.put(acc, :function, algorithm)
            acc

          (_empty_regex = Regex.run(~r/^$/, line)) != nil ->
            acc

          true ->
            acc
        end
      end)

    module_code =
      ["defmodule #{module_name} do"] ++
        Map.get(properties, :function, []) ++
        ["end"]

    IO.inspect(module_code)

    module_code
  end
end
