defmodule Models.Action do
  @moduledoc """
  Base type for defining an action
  """

  use TypedStruct

  typedstruct do
    @typedoc "Type for a condition"
  end

  # Should be Models.Action.t()
  @callback parse_action(Models.Function.Case.Metadata.t(), any()) :: any()

  # Should be List[Models.Action.t()]
  @spec parse_actions(Models.Function.Case.Metadata.t(), any()) :: List[any()]
  def parse_actions(metadata, body_ast) do
    IO.inspect(metadata)

    {_, actions} =
      Macro.postwalk(body_ast, [], fn node, acc ->
        action =
          case node do
            # Parse `if` action
            {:if, _, _} = if_ast ->
              Models.Action.If.parse_action(metadata, if_ast)

            # Parse `return value` action
            [do: {_value, _, nil} = return_value_ast] ->
              Models.Action.Return.Value.parse_action(metadata, return_value_ast)

            [else: {_value, _, nil} = return_value_ast] ->
              Models.Action.Return.Value.parse_action(metadata, return_value_ast)

            # Parse `return function` action
            [do: {_function, _, [_, _]} = return_function_ast] ->
              Models.Action.Return.Function.parse_action(metadata, return_function_ast)

            [else: {_function, _, [_, _]} = return_function_ast] ->
              Models.Action.Return.Function.parse_action(metadata, return_function_ast)

            # None of actions are matched
            _ ->
              nil
          end

        new_node =
          case action do
            nil -> node
            _ -> {}
          end

        new_acc =
          case action do
            nil -> acc
            _ -> acc ++ [action]
          end

        {new_node, new_acc}
      end)

    IO.inspect(actions)
    actions
  end
end
