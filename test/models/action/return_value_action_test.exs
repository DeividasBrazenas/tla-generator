defmodule Models.Action.Return.Value.Test do
  use ExUnit.Case
  doctest Models.Action.Return.Value

  describe "return value action" do
    test "is parsed" do
      # Arrange
      ast_token = [do: {:b, [line: 6], nil}]
      metadata = %Models.Function.Case.Metadata{
        name: :max
      }

      # Act
      action = Models.Action.Return.Value.parse_action(metadata, ast_token)

      # Assert
      assert action.value == :b
      assert action.function_name == :max
    end
  end
end
