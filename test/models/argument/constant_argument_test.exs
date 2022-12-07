defmodule Models.Type.Constant.Tests do
  use ExUnit.Case
  doctest Models.Type.Constant

  describe "constant argument" do
    test "is parsed" do
      # Act
      argument = Models.Type.Constant.parse_type(:a, %{name: nil})

      # Assert
      assert argument.value == :a
    end

    test "has constant" do
      # Arrange
      argument = %Models.Type.Constant{
        value: :a,
        name: nil
      }

      # Act
      has_constant = Models.Type.Constant.has_constant(argument)

      # Assert
      assert has_constant == true
    end
  end
end
