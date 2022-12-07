defmodule Generators.PlusCal.Procedure do
  alias Models.Common.Indent, as: Indent

  @spec generate_procedures(List[Models.Function.t()], List[atom()], Integer.t()) ::
          List[String.t()]
  def generate_procedures(functions, pluscal_processes, indent_level) do
    procedures =
      functions
      |> Enum.filter(fn function ->
        Enum.any?(pluscal_processes, fn procedure_name ->
          procedure_name == function.spec.name
        end)
      end)
      |> Enum.flat_map(fn function ->
        procedure = generate_procedure(function, indent_level)
        procedure ++ [""]
      end)

    procedures
  end

  @spec generate_procedure(Models.Function.t(), Integer.t()) :: List[String.t()]
  defp generate_procedure(function, indent_level) do
    procedure =
      [generate_header(function, indent_level)] ++
        generate_variables(function, indent_level) ++
        ["#{Indent.build(indent_level)}begin"] ++
        [generate_label(function.spec, indent_level + 1)] ++
        Generators.PlusCal.Body.generate_body(function.clauses, indent_level + 2) ++
        [generate_footer(indent_level)]

    procedure
  end

  @spec generate_header(Models.Function.t(), Integer.t()) :: String.t()
  defp generate_header(function, indent_level) do
    argument_names =
      Generators.Common.Argument.get_argument_names(function, "#{function.spec.name}")

    "#{Indent.build(indent_level)}procedure #{function.spec.name}(#{Enum.join(argument_names, ", ")})"
  end

  @spec generate_variables(Models.Function.t(), Integer.t()) :: List[String.t()]
  defp generate_variables(function, indent_level) do
    variables =
      function.clauses
      |> Enum.flat_map(fn clause -> clause.local_variables end)

    variables = variables |> Enum.uniq()

    case length(variables) > 0 do
      true -> ["#{Indent.build(indent_level)}variables #{Enum.join(variables, ", ")};"]
      false -> []
    end
  end

  @spec generate_footer(Integer.t()) :: String.t()
  defp generate_footer(indent_level) do
    footer = "#{Indent.build(indent_level)}end procedure;"
    footer
  end

  @spec generate_label(Models.Function.Spec.t(), Integer.t()) :: String.t()
  defp generate_label(spec, indent_level) do
    "#{Indent.build(indent_level)}#{spec.name}:"
  end
end
