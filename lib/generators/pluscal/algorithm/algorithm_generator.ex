defmodule Generators.PlusCal.Algorithm do
  alias Models.Common.Indent, as: Indent
  @tla_default_value_var "defaultInitValue"

  @spec generate_algorithm(String.t(), List[Models.Function.t()]) :: List[String.t()]
  def generate_algorithm(module_name, functions) do
    indent_level = 1

    algorithm =
      [generate_header(module_name)] ++
        [generate_result_variables(functions, indent_level)] ++
        [""] ++
        Generators.PlusCal.Algorithm.Procedure.generate_procedures(functions, indent_level) ++
        generate_main_body(functions, indent_level) ++
        [generate_footer()]

    IO.inspect(algorithm)
    algorithm
  end

  @spec generate_main_body(List[Models.Function.t()], Integer.t()) :: List[String.t()]
  defp generate_main_body(functions, indent_level) do
    body =
      functions
      |> Enum.flat_map(fn function -> generate_main_body_for_function(function, indent_level) end)

    ["#{Indent.build(indent_level)}begin"] ++ body
  end

  @spec generate_main_body_for_function(Models.Function.t(), Integer.t()) :: List[String.t()]
  defp generate_main_body_for_function(function, indent_level) do
    arguments = Generators.Common.Argument.get_arguments(function.clauses)

    function_body =
      ["#{Indent.build(indent_level + 1)}#{function.spec.name}:"] ++
        [
          "#{Indent.build(indent_level + 2)}if result_#{function.spec.name} = #{@tla_default_value_var} then"
        ] ++
        [
          "#{Indent.build(indent_level + 3)}call #{function.spec.name}(#{Enum.join(arguments, ", ")})"
        ] ++
        ["#{Indent.build(indent_level + 2)}end if;"]

    function_body
  end

  # Generates algorithm's result variables
  @spec generate_result_variables(List[Models.Function.t()], Integer.t()) :: String.t()
  defp generate_result_variables(functions, indent_level) do
    functions_with_result =
      functions
      |> Enum.filter(fn function -> function.spec.return_type != nil end)
      |> Enum.map(fn function -> "result_#{function.spec.name}" end)
      |> Enum.uniq()

    if length(functions_with_result) > 0 do
      "#{Indent.build(indent_level)}variables #{Enum.join(functions_with_result, ", ")}"
    else
      ""
    end
  end

  @spec generate_header(String.t()) :: String.t()
  def generate_header(module_name) do
    header = "(*--algorithm #{module_name}"
    header
  end

  @spec generate_footer() :: String.t()
  def generate_footer() do
    footer = "end algorithm; *)"
    footer
  end
end
