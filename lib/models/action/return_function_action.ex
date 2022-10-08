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
  def parse_action(_, do: {_function_name, _, _arguments} = function_call_ast) do
    action = %Models.Action.Return.Function{
      function_call: Macro.to_string(function_call_ast)
    }

    action
  end
end
