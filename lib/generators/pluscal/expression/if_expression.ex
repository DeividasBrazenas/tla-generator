defmodule Generators.PlusCal.Expression.If do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Expression

  @impl Generators.PlusCal.Expression
  @spec generate_expression(any(), List[Models.Type.t()], List[atom()], Integer.t()) ::
          List[String.t()]
  def generate_expression(
        %Models.Expression.If{} = expression,
        fn_inputs,
        local_variables,
        indent_level
      ) do
    expression =
      [
        "#{Indent.build(indent_level)}if #{Generators.Common.Condition.generate_clause_condition(expression.condition)} then"
      ] ++
        generate_condition_satisfied_expressions(
          expression.condition_satisfied_expressions,
          fn_inputs,
          local_variables,
          indent_level + 1
        ) ++
        generate_condition_unsatisfied_expressions(
          expression.condition_unsatisfied_expressions,
          fn_inputs,
          local_variables,
          indent_level + 1
        ) ++
        [
          "#{Indent.build(indent_level)}end if;"
        ]

    expression
  end

  @spec generate_condition_satisfied_expressions(
          List[Models.Expression.t()],
          List[Models.Type.t()],
          List[String.t()],
          Integer.t()
        ) ::
          List[String.t()]
  defp generate_condition_satisfied_expressions(
         expressions,
         fn_inputs,
         local_variables,
         indent_level
       ) do
    Generators.PlusCal.Expression.generate_expressions(
      expressions,
      fn_inputs,
      local_variables,
      indent_level
    )
  end

  @spec generate_condition_unsatisfied_expressions(
          List[Models.Expression.t()],
          List[Models.Type.t()],
          List[String.t()],
          Integer.t()
        ) ::
          List[String.t()]
  defp generate_condition_unsatisfied_expressions(
         expressions,
         fn_inputs,
         local_variables,
         indent_level
       ) do
    if length(expressions) > 0 do
      ["#{Indent.build(indent_level - 1)}else"] ++
        Generators.PlusCal.Expression.generate_expressions(
          expressions,
          fn_inputs,
          local_variables,
          indent_level
        )
    else
      []
    end
  end
end
