defmodule Models.Type.Struct.Tests do
  use ExUnit.Case
  doctest Models.Type.Struct

  describe "struct argument" do
    test "with name is parsed" do
      # Arrange
      ast = [{:__aliases__, [line: 1], [:Math]}, {:%{}, [line: 1], [operator: :<]}]

      # Act
      argument = Models.Type.Struct.parse_type(ast, %{name: :x})

      # Assert
      assert argument.type == :Math
      assert argument.name == :x

      assert argument.arguments == %Models.Type.Map{
               key_value_pairs: [operator: %Models.Type.Constant{value: :<}]
             }
    end

    test "without name is parsed" do
      # Arrange
      ast = [{:__aliases__, [line: 1], [:Math]}, {:%{}, [line: 1], [operator: :<]}]

      # Act
      argument = Models.Type.Struct.parse_type(ast, %{name: nil})

      # Assert
      assert argument.type == :Math
      assert argument.name == nil

      assert argument.arguments == %Models.Type.Map{
               key_value_pairs: [operator: %Models.Type.Constant{value: :<}]
             }
    end

    test "has constant" do
      # Arrange
      argument = %Models.Type.Struct{
        name: nil,
        type: :Math,
        arguments: %Models.Type.Map{
          key_value_pairs: [
            {:a,
             %Models.Type.Constant{
               value: :a,
               name: nil
             }}
          ],
          name: nil
        }
      }

      # Act
      has_constant = Models.Type.Struct.has_constant(argument)

      # Assert
      assert has_constant == true
    end

    test "has no constant" do
      # Arrange
      argument = %Models.Type.Struct{
        name: nil,
        type: :Math,
        arguments: %Models.Type.Map{
          key_value_pairs: [
            {:a,
             %Models.Type.Variable{
               name: :a
             }}
          ],
          name: nil
        }
      }

      # Act
      has_constant = Models.Type.Struct.has_constant(argument)

      # Assert
      assert has_constant == false
    end
  end
end
