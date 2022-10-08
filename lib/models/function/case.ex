defmodule Models.Function.Case do
  @moduledoc """
  Module defining the single function's case
  """
  use TypedStruct

  typedstruct do
    field(:metadata, Models.Function.Case.Metadata, default: nil)
    field(:actions, List[Models.Action.t()], default: [])
  end

  def parse_case(metadata, body_ast) do
    IO.inspect(body_ast)
    fn_case = %Models.Function.Case{
      metadata: metadata,
      actions: Models.Action.parse_actions(metadata, body_ast)
    }

    fn_case
  end
end
