defmodule Models.Type.Map.Tests do
  use ExUnit.Case
  doctest Models.Type.Map

  describe "map argument" do
    test "is parsed with constant arguments" do
      # Arrange
      ast = [operator: :<, right_operand: :a]

      # Act
      argument = Models.Type.Map.parse_type(ast, %{name: nil})

      # Assert
      assert length(argument.key_value_pairs) == 2

      assert Enum.at(argument.key_value_pairs, 0) ==
               {:operator, %Models.Type.Constant{value: :<}}

      assert Enum.at(argument.key_value_pairs, 1) ==
               {:right_operand, %Models.Type.Constant{value: :a}}
    end

    test "is parsed with tuple argument" do
      # Arrange
      ast = [operator: {:{}, [line: 1], [{:a, [line: 1], nil}]}]

      # Act
      argument = Models.Type.Map.parse_type(ast, %{name: nil})

      # Assert
      assert length(argument.key_value_pairs) == 1

      assert Enum.at(argument.key_value_pairs, 0) ==
               {:operator,
                %Models.Type.Tuple{arguments: [%Models.Type.Variable{name: :a}]}}
    end

    test "is parsed with map argument" do
      # Arrange
      ast = [operator: {:%{}, [line: 1], [a: :b]}]

      # Act
      argument = Models.Type.Map.parse_type(ast, %{name: nil})

      # Assert
      assert length(argument.key_value_pairs) == 1

      assert Enum.at(argument.key_value_pairs, 0) ==
               {:operator,
                %Models.Type.Map{
                  key_value_pairs: [{:a, %Models.Type.Constant{value: :b}}]
                }}
    end

    test "has constant" do
      # Arrange
      argument = %Models.Type.Map{
        key_value_pairs: [
          {:a,
           %Models.Type.Constant{
             value: :a,
             name: nil
           }}
        ],
        name: nil
      }

      # Act
      has_constant = Models.Type.Map.has_constant(argument)

      # Assert
      assert has_constant == true
    end

    test "has constant in inner argument" do
      # Arrange
      argument = %Models.Type.Map{
        key_value_pairs: [
          {:a,
           %Models.Type.Map{
             key_value_pairs: [
               {:a,
                %Models.Type.Constant{
                  value: :a,
                  name: nil
                }}
             ],
             name: nil
           }}
        ],
        name: nil
      }

      # Act
      has_constant = Models.Type.Map.has_constant(argument)

      # Assert
      assert has_constant == true
    end

    test "has no constant" do
      # Arrange
      argument = %Models.Type.Map{
        key_value_pairs: [
          {:a,
           %Models.Type.Variable{
             name: :a
           }}
        ],
        name: nil
      }

      # Act
      has_constant = Models.Type.Map.has_constant(argument)

      # Assert
      assert has_constant == false
    end
  end
end
