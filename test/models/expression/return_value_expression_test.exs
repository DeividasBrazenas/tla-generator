defmodule Models.Expression.Return.Value.Test do
  use ExUnit.Case
  doctest Models.Expression.Return.Value

  describe "return value expression" do
    test "is parsed" do
      # Arrange
      ast_token = {:b, [line: 6], nil}
      metadata = %Models.Function.Clause.Metadata{
        name: :max
      }

      # Act
      expression = Models.Expression.Return.Value.parse_expression(metadata, ast_token)

      # Assert
      assert expression.value == :b
      assert expression.function_name == :max
    end
  end
end
