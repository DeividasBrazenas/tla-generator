defmodule Models.Argument.Constant.Tests do
  use ExUnit.Case
  doctest Models.Argument.Constant

  describe "constant argument" do
    test "is parsed" do
      # Act
      argument = Models.Argument.Constant.parse_argument(:a, %{name: nil})

      # Assert
      assert argument.value == :a
    end

    test "has constant" do
      # Arrange
      argument = %Models.Argument.Constant{
        value: :a,
        name: nil
      }

      # Act
      has_constant = Models.Argument.Constant.has_constant(argument)

      # Assert
      assert has_constant == true
    end
  end
end
