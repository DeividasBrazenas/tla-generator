defmodule Models.Argument.Tuple.Tests do
  use ExUnit.Case
  doctest Models.Argument.Tuple

  describe "tuple argument" do
    test "is parsed with constant and variable arguments" do
      # Arrange
      ast = [:<, {:a, [line: 1], nil}, {:b, [line: 1], nil}]

      # Act
      argument = Models.Argument.Tuple.parse_argument(ast, nil)

      # Assert
      assert length(argument.arguments) == 3
      assert Enum.at(argument.arguments, 0) == %Models.Argument.Constant{value: :<}
      assert Enum.at(argument.arguments, 1) == %Models.Argument.Variable{name: :a}
      assert Enum.at(argument.arguments, 2) == %Models.Argument.Variable{name: :b}
    end

    test "is parsed with tuple arguments" do
      # Arrange
      ast = [:<, {:{}, [line: 1], [:<, {:a, [line: 1], nil}]}]

      # Act
      argument = Models.Argument.Tuple.parse_argument(ast, nil)

      # Assert
      assert length(argument.arguments) == 2
      assert Enum.at(argument.arguments, 0) == %Models.Argument.Constant{value: :<}

      assert Enum.at(argument.arguments, 1) == %Models.Argument.Tuple{
               arguments: [
                 %Models.Argument.Constant{value: :<},
                 %Models.Argument.Variable{name: :a}
               ]
             }
    end

    test "is parsed with map arguments" do
      # Arrange
      ast = [:<, {:%{}, [line: 34], [operator: {:%{}, [line: 1], [a: :b]}]}]

      # Act
      argument = Models.Argument.Tuple.parse_argument(ast, nil)

      # Assert
      assert length(argument.arguments) == 2
      assert Enum.at(argument.arguments, 0) == %Models.Argument.Constant{value: :<}

      assert Enum.at(argument.arguments, 1) == %Models.Argument.Map{
               key_value_pairs: [
                 operator: %Models.Argument.Map{
                   key_value_pairs: [a: %Models.Argument.Constant{value: :b}]
                 }
               ]
             }
    end
  end
end
