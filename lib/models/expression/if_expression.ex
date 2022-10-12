defmodule Models.Expression.If do
  @moduledoc """
  Defines `if` expression
  """
  @behaviour Models.Expression

  use TypedStruct

  typedstruct do
    field(:condition, Models.Common.Condition.t(), default: nil, enforce: true)
    field(:condition_satisfied_expressions, List[Models.Expression.t()], default: [])
    field(:condition_unsatisfied_expressions, List[Models.Expression.t()], default: [])
  end

  @impl Models.Expression
  @spec parse_expression(Models.Function.Clause.Metadata.t(), any()) :: any()
  def parse_expression(metadata, {:if, _, [condition, expressions_ast]}) do
    {do_expressions, else_expressions} = get_inner_expressions(metadata, expressions_ast)

    expression = %Models.Expression.If{
      condition: Models.Common.Condition.parse_condition(condition),
      condition_satisfied_expressions: do_expressions,
      condition_unsatisfied_expressions: else_expressions
    }

    expression
  end

  @spec get_inner_expressions(Models.Function.Clause.Metadata.t(), any()) ::
          {List[Models.Expression.t()], List[Models.Expression.t()]}
  defp get_inner_expressions(metadata, [do_ast, else_ast]) do
    do_expressions = Models.Expression.parse_expressions(metadata, [do_ast])
    else_expressions = Models.Expression.parse_expressions(metadata, [else_ast])
    {do_expressions, else_expressions}
  end

  defp get_inner_expressions(metadata, [do_ast]) do
    do_expressions = Models.Expression.parse_expressions(metadata, [do_ast])
    {do_expressions, []}
  end
end
