defmodule Models.Argument.Constant.Tests do
  use ExUnit.Case
  doctest Models.Argument.Constant

  describe "constant argument" do
    test "is parsed" do
      # Act
      argument = Models.Argument.Constant.parse_argument(:a, nil)

      # Assert
      assert argument.value == :a
    end
  end
end
