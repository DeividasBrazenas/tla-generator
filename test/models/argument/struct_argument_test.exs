defmodule Models.Argument.Struct.Tests do
  use ExUnit.Case
  doctest Models.Argument.Struct

  describe "struct argument" do
    test "with name is parsed" do
      # Arrange
      ast = [{:__aliases__, [line: 1], [:Math]}, {:%{}, [line: 1], [operator: :<]}]

      # Act
      argument = Models.Argument.Struct.parse_argument(ast, %{name: :x})

      # Assert
      assert argument.type == :Math
      assert argument.name == :x

      assert argument.arguments == %Models.Argument.Map{
               key_value_pairs: [operator: %Models.Argument.Constant{value: :<}]
             }
    end

    test "without name is parsed" do
      # Arrange
      ast = [{:__aliases__, [line: 1], [:Math]}, {:%{}, [line: 1], [operator: :<]}]

      # Act
      argument = Models.Argument.Struct.parse_argument(ast, %{name: nil})

      # Assert
      assert argument.type == :Math
      assert argument.name == nil

      assert argument.arguments == %Models.Argument.Map{
               key_value_pairs: [operator: %Models.Argument.Constant{value: :<}]
             }
    end

    test "has constant" do
      # Arrange
      argument = %Models.Argument.Struct{
        name: nil,
        type: :Math,
        arguments: %Models.Argument.Map{
          key_value_pairs: [
            {:a,
             %Models.Argument.Constant{
               value: :a,
               name: nil
             }}
          ],
          name: nil
        }
      }

      # Act
      has_constant = Models.Argument.Struct.has_constant(argument)

      # Assert
      assert has_constant == true
    end

    test "has no constant" do
      # Arrange
      argument = %Models.Argument.Struct{
        name: nil,
        type: :Math,
        arguments: %Models.Argument.Map{
          key_value_pairs: [
            {:a,
             %Models.Argument.Variable{
               name: :a
             }}
          ],
          name: nil
        }
      }

      # Act
      has_constant = Models.Argument.Struct.has_constant(argument)

      # Assert
      assert has_constant == false
    end
  end
end
