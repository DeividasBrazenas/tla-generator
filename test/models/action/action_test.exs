defmodule Models.Action.Test do
  use ExUnit.Case
  doctest Models.Action

  describe "actions" do
    test "are parsed" do
      # Arrange
      ast_token = [do: {:b, [line: 6], nil}]
      metadata = %Models.Function.Case.Metadata{
        name: :max
      }
      # Act
      actions = Models.Action.parse_actions(metadata, ast_token)

      # Assert
      assert length(actions) == 1

      action = List.first(actions)
      assert action.__struct__ == Models.Action.Return.Value
      assert action.value == :b
      assert action.function_name == :max
    end
  end
end
