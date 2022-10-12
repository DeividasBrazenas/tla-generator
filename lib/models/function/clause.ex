defmodule Models.Function.Clause do
  @moduledoc """
  Module defining the single function's clause
  """
  use TypedStruct

  typedstruct do
    field(:metadata, Models.Function.Clause.Metadata, default: nil)
    field(:expressions, List[Models.Expression.t()], default: [])
  end

  def parse_clause(metadata, body_ast) do
    fn_clause = %Models.Function.Clause{
      metadata: metadata,
      expressions: Models.Expression.parse_expressions(metadata, body_ast)
    }

    fn_clause
  end
end
