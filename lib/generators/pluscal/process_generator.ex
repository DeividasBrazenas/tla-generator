defmodule Generators.PlusCal.Process do
  alias Models.Common.Indent, as: Indent

  @spec generate_processes(List[Models.Function.t()], List[atom()], Integer.t()) ::
          List[String.t()]
  def generate_processes(functions, pluscal_processes, indent_level) do
    processes =
      functions
      |> Enum.filter(fn function ->
        Enum.any?(pluscal_processes, fn process_name ->
          process_name == function.spec.name
        end)
      end)
      |> Enum.flat_map(fn function ->
        process = generate_process(function, indent_level)
        process ++ [""]
      end)

    processes
  end

  @spec generate_process(Models.Function.t(), Integer.t()) :: List[String.t()]
  defp generate_process(function, indent_level) do
    process =
      [generate_header(function, indent_level)] ++
        generate_variables(function, indent_level) ++
        ["#{Indent.build(indent_level)}begin"] ++
        [generate_label(function.spec, indent_level + 1)] ++
        Generators.PlusCal.Body.generate_body(function.clauses, indent_level + 2) ++
        [generate_footer(indent_level)]

    process
  end

  @spec generate_header(Models.Function.t(), Integer.t()) :: String.t()
  defp generate_header(function, indent_level) do
    "#{Indent.build(indent_level)}process #{function.spec.name} = \"#{function.spec.name}\""
  end

  @spec generate_variables(Models.Function.t(), Integer.t()) :: List[String.t()]
  defp generate_variables(function, indent_level) do
    input_variables =
      Generators.Common.Argument.get_argument_names(function, "")
      |> Enum.map(fn arg_name -> "#{arg_name} = input_#{function.spec.name}_#{arg_name}" end)

    local_variables =
      function.clauses
      |> Enum.flat_map(fn clause -> clause.local_variables end)

    variables = Enum.concat(input_variables, local_variables) |> Enum.uniq()

    case length(variables) > 0 do
      true -> ["#{Indent.build(indent_level)}variables #{Enum.join(variables, ", ")};"]
      false -> []
    end
  end

  @spec generate_footer(Integer.t()) :: String.t()
  defp generate_footer(indent_level) do
    footer = "#{Indent.build(indent_level)}end process;"
    footer
  end

  @spec generate_label(Models.Function.Spec.t(), Integer.t()) :: String.t()
  defp generate_label(spec, indent_level) do
    "#{Indent.build(indent_level)}#{spec.name}:"
  end
end
