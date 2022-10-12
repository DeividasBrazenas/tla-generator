defmodule Generators.PlusCal.Algorithm.Procedure do
  alias Models.Common.Indent, as: Indent

  @spec generate_procedures(List[Models.Function.t()], Integer.t()) :: List[String.t()]
  def generate_procedures(functions, indent_level) do
    procedures =
      functions
      |> Enum.flat_map(fn function ->
        procedure = generate_procedure(function.spec, function.clauses, indent_level)
        procedure ++ [""]
      end)

    IO.inspect(procedures)
    procedures
  end

  @spec generate_procedure(Models.Function.Spec.t(), List[Models.Function.Clause.t()], Integer.t()) ::
          List[String.t()]
  defp generate_procedure(spec, clauses, indent_level) do
    procedure =
      generate_header(spec, clauses, indent_level) ++
        [generate_label(spec, indent_level + 1)] ++
        generate_body(clauses, indent_level + 2) ++
        [generate_footer(indent_level)]

    IO.inspect(procedure)
    procedure
  end

  @spec generate_body(List[Models.Function.Clause.t()], Integer.t()) :: List[String.t()]
  defp generate_body(clauses, indent_level) do
    clauses_count = length(clauses)

    if clauses_count > 1 do
      {generated_clauses, _} =
        clauses
        |> Enum.flat_map_reduce(1, fn fn_clause, fn_clause_number ->
          generated_clause = generate_clause(fn_clause, fn_clause_number, clauses_count, indent_level)
          {generated_clause, fn_clause_number + 1}
        end)

      body =
        generated_clauses ++
          ["#{Indent.build(indent_level)}end if;"]

      body
    else
      generate_clause(List.first(clauses), 1, clauses_count, indent_level)
    end
  end

  @spec generate_clause(Models.Function.Clause.t(), Integer.t(), Integer.t(), Integer.t()) ::
          List[String.t()]
  defp generate_clause(fn_clause, clause_number, clauses_count, indent_level) do
    generated_condition =
      case clauses_count do
        #
        1 -> [] # Only one clause in function, so no need to generate condition
        _ -> generate_condition(fn_clause.metadata.condition, clause_number, indent_level)
      end

    new_indent_level =
      case generated_condition do
        [] -> indent_level # There's no condition label, so no need to increase indent
        _ -> indent_level + 1
      end

    generated_clause =
      generated_condition ++
        Generators.PlusCal.Algorithm.Procedure.Expression.generate_expressions(
          fn_clause.expressions,
          new_indent_level
        )

    generated_clause
  end

  @spec generate_condition(
          Models.Common.Condition.t(),
          Integer.t(),
          Integer.t()
        ) ::
          List[String.t()]
  defp generate_condition(condition, clause_number, indent_level) do
    condition_keyword =
      case {condition, clause_number} do
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

  @spec generate_header(Models.Function.Spec.t(), List[Models.Function.Clause.t()], Integer.t()) ::
          List[String.t()]
  defp generate_header(spec, clauses, indent_level) do
    arguments = Generators.Common.Argument.get_arguments(clauses)

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
