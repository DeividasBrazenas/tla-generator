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
  @spec parse_expression(any(), Models.Function.Clause.Metadata.t()) :: Models.Expression.If.t()
  def parse_expression({:if, _, [condition, expressions_ast]}, metadata) do
    {do_expressions, else_expressions} = get_inner_expressions(expressions_ast, metadata)

    expression = %Models.Expression.If{
      condition: Models.Common.Condition.parse_condition(condition),
      condition_satisfied_expressions: do_expressions,
      condition_unsatisfied_expressions: else_expressions
    }

    expression
  end

  @spec get_inner_expressions(any(), Models.Function.Clause.Metadata.t()) ::
          {List[Models.Expression.t()], List[Models.Expression.t()]}
  defp get_inner_expressions([do_ast, else_ast], metadata) do
    do_expressions = Models.Expression.parse_expressions([do_ast], metadata)
    else_expressions = Models.Expression.parse_expressions([else_ast], metadata)
    {do_expressions, else_expressions}
  end

  defp get_inner_expressions([do_ast], metadata) do
    do_expressions = Models.Expression.parse_expressions([do_ast], metadata)
    {do_expressions, []}
  end
end
