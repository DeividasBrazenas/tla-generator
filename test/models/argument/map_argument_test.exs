defmodule Models.Argument.Map.Tests do
  use ExUnit.Case
  doctest Models.Argument.Map

  describe "map argument" do
    test "is parsed with constant arguments" do
      # Arrange
      ast = [operator: :<, right_operand: :a]

      # Act
      argument = Models.Argument.Map.parse_argument(ast, nil)

      # Assert
      assert length(argument.key_value_pairs) == 2

      assert Enum.at(argument.key_value_pairs, 0) ==
               {:operator, %Models.Argument.Constant{value: :<}}

      assert Enum.at(argument.key_value_pairs, 1) ==
               {:right_operand, %Models.Argument.Constant{value: :a}}
    end

    test "is parsed with tuple argument" do
      # Arrange
      ast = [operator: {:{}, [line: 1], [{:a, [line: 1], nil}]}]

      # Act
      argument = Models.Argument.Map.parse_argument(ast, nil)

      IO.inspect(argument)
      # Assert
      assert length(argument.key_value_pairs) == 1

      assert Enum.at(argument.key_value_pairs, 0) ==
               {:operator,
                %Models.Argument.Tuple{arguments: [%Models.Argument.Variable{name: :a}]}}
    end

    test "is parsed with map argument" do
      # Arrange
      ast = [operator: {:%{}, [line: 1], [a: :b]}]

      # Act
      argument = Models.Argument.Map.parse_argument(ast, nil)

      IO.inspect(argument)
      # Assert
      assert length(argument.key_value_pairs) == 1

      assert Enum.at(argument.key_value_pairs, 0) ==
               {:operator,
                %Models.Argument.Map{key_value_pairs: [{:a, %Models.Argument.Constant{value: :b}}]}}
    end
  end
end
