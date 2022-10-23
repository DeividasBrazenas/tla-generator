defmodule Generators.PlusCal.Algorithm.Procedure do
  alias Models.Common.Indent, as: Indent

  @spec generate_procedures(List[Models.Function.t()], Integer.t()) :: List[String.t()]
  def generate_procedures(functions, indent_level) do
    IO.inspect(functions)

    procedures =
      functions
      |> Enum.flat_map(fn function ->
        procedure = generate_procedure(function, indent_level)
        procedure ++ [""]
      end)

    IO.inspect(procedures)
    procedures
  end

  @spec generate_procedure(Models.Function.t(), Integer.t()) :: List[String.t()]
  defp generate_procedure(function, indent_level) do
    procedure =
      generate_header(function, indent_level) ++
        [generate_label(function.spec, indent_level + 1)] ++
        generate_body(function.clauses, indent_level + 2) ++
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
          generated_clause =
            generate_clause(fn_clause, fn_clause_number, clauses_count, indent_level)

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
    IO.inspect(fn_clause)
    generated_condition =
      case clauses_count do
        #
        # Only one clause in function, so no need to generate condition
        1 -> []
        _ -> generate_condition(fn_clause.metadata, clause_number, indent_level)
      end

    new_indent_level =
      case generated_condition do
        # There's no condition label, so no need to increase indent
        [] -> indent_level
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
          Models.Function.Clause.Metadata.t(),
          Integer.t(),
          Integer.t()
        ) ::
          List[String.t()]
  defp generate_condition(metadata, clause_number, indent_level) do
    IO.inspect(metadata)
    arguments_with_constants = Models.Argument.get_arguments_with_constants(metadata.arguments)

    condition_keyword =
      case {metadata.condition, clause_number} do
        {nil, _} -> "else"
        {_, 1} -> "if"
        {_, _} -> "elsif"
      end

    if condition_keyword === "else" do
      ["#{Indent.build(indent_level)}#{condition_keyword}"]
    else
      [
        "#{Indent.build(indent_level)}#{condition_keyword} #{Generators.Common.Condition.generate_condition(metadata.condition)} then"
      ]
    end
  end

  @spec generate_header(Models.Function.t(), Integer.t()) :: List[String.t()]
  defp generate_header(function, indent_level) do
    argument_names = Generators.Common.Argument.get_argument_names(function, "")
    IO.inspect(argument_names)

    header =
      [
        "#{Indent.build(indent_level)}procedure #{function.spec.name}(#{Enum.join(argument_names, ", ")})"
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
