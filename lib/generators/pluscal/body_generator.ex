defmodule Generators.PlusCal.Body do
  alias Models.Common.Indent, as: Indent

  @spec generate_body(List[Models.Function.Clause.t()], Integer.t()) :: List[String.t()]
  def generate_body(clauses, indent_level) do
    clauses_count = length(clauses)

    IO.inspect(clauses_count)

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
      body = generate_clause(List.first(clauses), 1, clauses_count, indent_level)

      if String.contains?(Enum.at(body, 0), "if") do
        body ++ ["#{Indent.build(indent_level)}end if;"]
      else
        body
      end
    end
  end

  @spec generate_clause(Models.Function.Clause.t(), Integer.t(), Integer.t(), Integer.t()) ::
          List[String.t()]
  defp generate_clause(fn_clause, clause_number, clauses_count, indent_level) do
    IO.inspect(fn_clause)

    arguments_with_constants =
      Models.Argument.get_arguments_with_constants(fn_clause.metadata.arguments)

    generated_condition =
      generate_condition(
        fn_clause.metadata.condition,
        arguments_with_constants,
        clause_number,
        clause_number == clauses_count,
        indent_level
      )

    IO.inspect(generated_condition)

    new_indent_level =
      case length(generated_condition) do
        # There's no condition label, so no need to increase indent
        0 -> indent_level
        1 -> indent_level + 1
        _ -> indent_level + 2
      end

    generated_clause =
      generated_condition ++
        Generators.PlusCal.Expression.generate_expressions(
          fn_clause.expressions,
          fn_clause.metadata.arguments,
          new_indent_level
        )

    generated_clause
  end

  @spec generate_condition(
          Models.Common.Condition.t(),
          List[Models.Argument.t()],
          Integer.t(),
          boolean(),
          Integer.t()
        ) ::
          List[String.t()]
  defp generate_condition(nil, [], _, false, _), do: []

  defp generate_condition(
         clause_condition,
         arguments_with_constant,
         clause_number,
         last_clause,
         indent_level
       ) do
    conditions =
      Generators.Common.Condition.generate_conditions(clause_condition, arguments_with_constant)

    condition_keyword =
      case {length(conditions), clause_number, last_clause} do
        {_, 1, _} -> "if"
        {0, 1, _} -> nil
        {_, _, false} -> "elsif"
        {_, _, true} -> "else"
      end

    IO.inspect(conditions)

    if condition_keyword === "else" do
      ["#{Indent.build(indent_level)}else"]
    else
      case length(conditions) do
        0 ->
          []

        1 ->
          ["#{Indent.build(indent_level)}#{condition_keyword} #{Enum.at(conditions, 0)} then"]

        _ ->
          first_condition = conditions |> Enum.at(0)
          last_condition = conditions |> Enum.at(-1)
          other_conditions = conditions |> Enum.slice(1..-2)

          IO.inspect(first_condition)

          ["#{Indent.build(indent_level)}#{condition_keyword} #{first_condition}"] ++
            Enum.map(other_conditions, fn c -> "#{Indent.build(indent_level + 1)}#{c}" end) ++
            ["#{Indent.build(indent_level + 1)}#{last_condition} then"]
      end
    end
  end
end
