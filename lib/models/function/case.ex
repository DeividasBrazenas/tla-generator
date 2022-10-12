defmodule Models.Function.Case do
  @moduledoc """
  Module defining the single function's case
  """
  use TypedStruct

  typedstruct do
    field(:metadata, Models.Function.Case.Metadata, default: nil)
    field(:expressions, List[Models.Expression.t()], default: [])
  end

  def parse_case(metadata, body_ast) do
    fn_case = %Models.Function.Case{
      metadata: metadata,
      expressions: Models.Expression.parse_expressions(metadata, body_ast)
    }

    fn_case
  end
end
