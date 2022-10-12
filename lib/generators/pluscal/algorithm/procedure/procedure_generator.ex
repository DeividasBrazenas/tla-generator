defmodule Generators.PlusCal.Algorithm.Procedure do
  alias Models.Common.Indent, as: Indent

  @spec generate_procedures(List[Models.Function.t()], Integer.t()) :: List[String.t()]
  def generate_procedures(functions, indent_level) do
    procedures =
      functions
      |> Enum.flat_map(fn function ->
        procedure = generate_procedure(function.spec, function.cases, indent_level)
        procedure ++ [""]
      end)

    IO.inspect(procedures)
    procedures
  end

  @spec generate_procedure(Models.Function.Spec.t(), List[Models.Function.Case.t()], Integer.t()) ::
          List[String.t()]
  defp generate_procedure(spec, cases, indent_level) do
    procedure =
      generate_header(spec, cases, indent_level) ++
        [generate_label(spec, indent_level + 1)] ++
        generate_body(cases, indent_level + 2) ++
        [generate_footer(indent_level)]

    IO.inspect(procedure)
    procedure
  end

  @spec generate_body(List[Models.Function.Case.t()], Integer.t()) :: List[String.t()]
  defp generate_body(cases, indent_level) do
    cases_count = length(cases)

    if cases_count > 1 do
      {generated_cases, _} =
        cases
        |> Enum.flat_map_reduce(1, fn fn_case, fn_case_number ->
          generated_case = generate_case(fn_case, fn_case_number, cases_count, indent_level)
          {generated_case, fn_case_number + 1}
        end)

      body =
        generated_cases ++
          ["#{Indent.build(indent_level)}end if;"]

      body
    else
      generate_case(List.first(cases), 1, cases_count, indent_level)
    end
  end

  @spec generate_case(Models.Function.Case.t(), Integer.t(), Integer.t(), Integer.t()) ::
          List[String.t()]
  defp generate_case(fn_case, case_number, cases_count, indent_level) do
    generated_condition =
      case cases_count do
        #
        1 -> [] # Only one case in function, so no need to generate condition
        _ -> generate_condition(fn_case.metadata.condition, case_number, indent_level)
      end

    new_indent_level =
      case generated_condition do
        [] -> indent_level # There's no condition label, so no need to increase indent
        _ -> indent_level + 1
      end

    generated_case =
      generated_condition ++
        Generators.PlusCal.Algorithm.Procedure.Expression.generate_expressions(
          fn_case.expressions,
          new_indent_level
        )

    generated_case
  end

  @spec generate_condition(
          Models.Common.Condition.t(),
          Integer.t(),
          Integer.t()
        ) ::
          List[String.t()]
  defp generate_condition(condition, case_number, indent_level) do
    condition_keyword =
      case {condition, case_number} do
        {nil, _} -> "else"
        {_, 1} -> "if"
        {_, _} -> "elsif"
      end

    if condition_keyword === "else" do
      ["#{Indent.build(indent_level)}#{condition_keyword}"]
    else
      [
        "#{Indent.build(indent_level)}#{condition_keyword} #{Generators.Common.Condition.generate_condition(condition)} then"
      ]
    end
  end

  @spec generate_header(Models.Function.Spec.t(), List[Models.Function.Case.t()], Integer.t()) ::
          List[String.t()]
  defp generate_header(spec, cases, indent_level) do
    arguments = Generators.Common.Argument.get_arguments(cases)

    header =
      [
        "#{Indent.build(indent_level)}procedure #{spec.name}(#{Enum.join(arguments, ", ")})"
      ] ++
        ["#{Indent.build(indent_level)}begin"]

    header
  end

  @spec generate_footer(Integer.t()) :: String.t()
  defp generate_footer(indent_level) do
    footer = "#{Indent.build(indent_level)}end procedure"
    footer
  end

  @spec generate_label(Models.Function.Spec.t(), Integer.t()) :: String.t()
  defp generate_label(spec, indent_level) do
    "#{Indent.build(indent_level)}#{spec.name}:"
  end
end
