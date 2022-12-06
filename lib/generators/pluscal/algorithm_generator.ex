defmodule Generators.PlusCal.Algorithm do
  alias Models.Common.Indent, as: Indent
  @tla_default_value_var "defaultInitValue"

  @spec generate_algorithm(String.t(), List[Models.Function.t()], List[atom()], List[atom()]) ::
          List[String.t()]
  def generate_algorithm(module_name, functions, pluscal_processes, pluscal_procedures) do
    IO.inspect(functions)
    indent_level = 1

    algorithm =
      [generate_header(module_name)] ++
        [generate_result_variables(pluscal_processes, pluscal_procedures, indent_level)] ++
        [""] ++
        Generators.PlusCal.Procedure.generate_procedures(
          functions,
          pluscal_procedures,
          indent_level
        ) ++
        [""] ++
        Generators.PlusCal.Process.generate_processes(
          functions,
          pluscal_processes,
          indent_level
        ) ++
        [generate_footer()]

    IO.inspect(algorithm)
    algorithm
  end

  # Generates algorithm's result variables
  @spec generate_result_variables(List[atom()], List[atom()], Integer.t()) :: String.t()
  defp generate_result_variables(pluscal_processes, pluscal_procedures, indent_level) do
    result_variables =
      pluscal_processes
      |> Enum.map(fn p -> "result_#{p}" end)
      |> Enum.concat(
        pluscal_procedures
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
