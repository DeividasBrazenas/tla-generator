defmodule Generators.PlusCal.Algorithm do
  alias Models.Common.Indent, as: Indent
  @tla_default_value_var "defaultInitValue"

  @spec generate_algorithm(String.t(), List[Models.Function.t()], List[atom()], List[atom()]) ::
          List[String.t()]
  def generate_algorithm(module_name, functions, pluscal_procedures, pluscal_macros) do
    IO.inspect(functions)
    indent_level = 1

    algorithm =
      [generate_header(module_name)] ++
        [generate_result_variables(pluscal_procedures, pluscal_macros, indent_level)] ++
        [""] ++
        Generators.PlusCal.Algorithm.Macro.generate_macros(
          functions,
          pluscal_macros,
          indent_level
        ) ++
        [""] ++
        Generators.PlusCal.Algorithm.Procedure.generate_procedures(
          functions,
          pluscal_procedures,
          indent_level
        ) ++
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
    argument_names = Generators.Common.Argument.get_argument_names(function, "in_")

    function_body =
      ["#{Indent.build(indent_level + 1)}#{function.spec.name}:"] ++
        [
          "#{Indent.build(indent_level + 2)}if result_#{function.spec.name} = #{@tla_default_value_var} then"
        ] ++
        [
          "#{Indent.build(indent_level + 3)}call #{function.spec.name}(#{Enum.join(argument_names, ", ")})"
        ] ++
        ["#{Indent.build(indent_level + 2)}end if;"]

    function_body
  end

  # Generates algorithm's result variables
  @spec generate_result_variables(List[atom()], List[atom()], Integer.t()) :: String.t()
  defp generate_result_variables(pluscal_procedures, pluscal_macros, indent_level) do
    result_variables =
      pluscal_procedures
      |> Enum.map(fn p -> "result_#{p}" end)
      |> Enum.concat(
        pluscal_macros
        |> Enum.map(fn m -> "result_#{m}" end)
      )
      |> Enum.uniq()

    if length(result_variables) > 0 do
      "#{Indent.build(indent_level)}variables #{Enum.join(result_variables, ", ")}"
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
