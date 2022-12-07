defmodule Models.Type.Tuple.Tests do
  use ExUnit.Case
  doctest Models.Type.Tuple

  describe "tuple argument" do
    test "is parsed with constant and variable arguments" do
      # Arrange
      ast = [:<, {:a, [line: 1], nil}, {:b, [line: 1], nil}]

      # Act
      argument = Models.Type.Tuple.parse_type(ast, %{name: nil})

      # Assert
      assert length(argument.arguments) == 3
      assert Enum.at(argument.arguments, 0) == %Models.Type.Constant{value: :<}
      assert Enum.at(argument.arguments, 1) == %Models.Type.Variable{name: :a}
      assert Enum.at(argument.arguments, 2) == %Models.Type.Variable{name: :b}
    end

    test "is parsed with tuple arguments" do
      # Arrange
      ast = [:<, {:{}, [line: 1], [:<, {:a, [line: 1], nil}]}]

      # Act
      argument = Models.Type.Tuple.parse_type(ast, %{name: nil})

      # Assert
      assert length(argument.arguments) == 2
      assert Enum.at(argument.arguments, 0) == %Models.Type.Constant{value: :<}

      assert Enum.at(argument.arguments, 1) == %Models.Type.Tuple{
               arguments: [
                 %Models.Type.Constant{value: :<},
                 %Models.Type.Variable{name: :a}
               ]
             }
    end

    test "is parsed with map arguments" do
      # Arrange
      ast = [:<, {:%{}, [line: 34], [operator: {:%{}, [line: 1], [a: :b]}]}]

      # Act
      argument = Models.Type.Tuple.parse_type(ast, %{name: nil})

      # Assert
      assert length(argument.arguments) == 2
      assert Enum.at(argument.arguments, 0) == %Models.Type.Constant{value: :<}

      assert Enum.at(argument.arguments, 1) == %Models.Type.Map{
               key_value_pairs: [
                 operator: %Models.Type.Map{
                   key_value_pairs: [a: %Models.Type.Constant{value: :b}]
                 }
               ]
             }
    end

    test "has constant" do
      # Arrange
      argument = %Models.Type.Tuple{
        arguments: [%Models.Type.Map{
          key_value_pairs: [
            {:a,
             %Models.Type.Constant{
               value: :a,
               name: nil
             }}
          ],
          name: nil
        }]
      }

      # Act
      has_constant = Models.Type.Tuple.has_constant(argument)

      # Assert
      assert has_constant == true
    end

    test "has constant in inner argument" do
      # Arrange
      argument = %Models.Type.Tuple{
        arguments: [%Models.Type.Map{
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
        }]
      }

      # Act
      has_constant = Models.Type.Tuple.has_constant(argument)

      # Assert
      assert has_constant == true
    end

    test "has no constant" do
      # Arrange
      argument = %Models.Type.Tuple{
        arguments: [%Models.Type.Map{
          key_value_pairs: [
            {:a,
             %Models.Type.Variable{
               name: :a
             }}
          ],
          name: nil
        }]
      }

      # Act
      has_constant = Models.Type.Tuple.has_constant(argument)

      # Assert
      assert has_constant == false
    end
  end
end
