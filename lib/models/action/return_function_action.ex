defmodule Models.Action.Return.Function do
  @moduledoc """
  Defines `if` action
  """
  @behaviour Models.Action

  use TypedStruct

  typedstruct do
    field(:function_call, String.t(), default: nil, enforce: true)
    field(:arguments, List[any()], default: [])
  end

  @impl Models.Action
  # Should be Models.Action.If.t()
  @spec parse_action(Models.Function.Case.Metadata.t(), any()) :: any()
  def parse_action(_, return_ast) do
    function_call = Macro.to_string(return_ast)

    action = %Models.Action.Return.Function{
      function_call: function_call
    }

    action
  end
end
