defmodule Models.Function.Case.Metadata.Tests do
  use ExUnit.Case
  doctest Models.Function.Case.Metadata

  describe "metadata" do
    test "is parsed with condition" do
      # Arrange
      ast_token = {:when, [line: 6], [{:max, [line: 6], [{:a, [line: 6], nil}, {:b, [line: 6], nil}]}, {:<, [line: 6], [{:a, [line: 6], nil}, {:b, [line: 6], nil}]}]}

      # Act
      metadata = Models.Function.Case.Metadata.parse_metadata(ast_token)

      # Assert
      assert metadata.name == :max
      assert metadata.arguments == [:a, :b]
      assert metadata.condition.operator == :<
      assert metadata.condition.left_operand == :a
      assert metadata.condition.right_operand == :b
    end

    test "is parsed without condition" do
      # Arrange
      ast_token = {:max, [line: 7], [{:a, [line: 7], nil}, {:b, [line: 7], nil}]}

      # Act
      metadata = Models.Function.Case.Metadata.parse_metadata(ast_token)

      # Assert
      assert metadata.name == :max
      assert metadata.arguments == [:a, :b]
      assert metadata.condition == nil
    end
  end
end
