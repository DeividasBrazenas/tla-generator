defmodule Models.Expression.Test do
  use ExUnit.Case
  doctest Models.Expression

  describe "expressions" do
    test "are parsed" do
      # Arrange
      ast_token = [do: {:b, [line: 6], nil}]
      metadata = %Models.Function.Clause.Metadata{
        name: :max
      }
      # Act
      expressions = Models.Expression.parse_expressions(metadata, ast_token)

      # Assert
      assert length(expressions) == 1

      expression = List.first(expressions)
      assert expression.__struct__ == Models.Expression.Return.Value
      assert expression.value == :b
      assert expression.function_name == :max
    end
  end
end
