defmodule Models.Common.Condition.Tests do
  use ExUnit.Case
  doctest Models.Common.Condition

  describe "condition" do
    test "is parsed" do
      # Arrange
      ast_token = {:<, [line: 6], [{:a, [line: 6], nil}, {:b, [line: 6], nil}]}

      # Act
      condition = Models.Common.Condition.parse_condition(ast_token)

      # Assert
      assert condition.operator == :<
      assert condition.left_operand == :a
      assert condition.right_operand == :b
    end
  end
end
