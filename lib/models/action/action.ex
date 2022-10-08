defmodule Models.Action do
  @moduledoc """
  Base type for defining an action
  """

  use TypedStruct

  typedstruct do
    @typedoc "Type for a condition"
  end

  @callback parse_action(Models.Function.Case.Metadata.t(), any()) :: any() # Should be Models.Action.t()

  @spec parse_actions(Models.Function.Case.Metadata.t(), any()) :: List[any()] # Should be List[Models.Action.t()]
  def parse_actions(metadata, body_ast) do
    IO.inspect(metadata)
    {_, actions} = Macro.postwalk({metadata, body_ast}, [], &parse_action/2)
    IO.inspect(actions)
    actions

  end

  # Probably metadata is passed incorrectly here....
  @spec parse_action(any(), List[Models.Action.t()]) :: {any(), List[Models.Action.t()]}
  defp parse_action({metadata, [do: {_value, _, nil}] = node}, acc) do
    IO.inspect(metadata)
    action = Models.Action.Return.Value.parse_action(metadata, node)
    {{metadata, node}, acc ++ [action]}
  end

  @spec parse_action(any(), List[Models.Action.t()]) :: {any(), List[Models.Action.t()]}
  defp parse_action({metadata, [do: {_function, _, [_, _]}] = node}, acc) do
    IO.inspect(metadata)
    action = Models.Action.Return.Function.parse_action(metadata, node)
    {{metadata, node}, acc ++ [action]}
  end

  defp parse_action(node, acc), do: {node, acc}
end
