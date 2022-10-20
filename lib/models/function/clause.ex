defmodule Models.Function.Clause do
  @moduledoc """
  Module defining the single function's clause
  """
  use TypedStruct

  typedstruct do
    field(:metadata, Models.Function.Clause.Metadata.t(), default: nil)
    field(:expressions, List[Models.Expression.t()], default: [])
  end

  @spec parse_clause(Models.Function.Clause.Metadata.t(), any()) :: Models.Function.Clause.t()
  def parse_clause(metadata, body_ast) do
    fn_clause = %Models.Function.Clause{
      metadata: metadata,
      expressions: Models.Expression.parse_expressions(body_ast, metadata)
    }

    fn_clause
  end
end
