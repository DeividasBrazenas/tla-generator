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
  end
end
