defmodule Models.Argument.Variable.Tests do
  use ExUnit.Case
  doctest Models.Argument.Variable

  describe "variable argument" do
    test "is parsed" do
      # Act
      argument = Models.Argument.Variable.parse_argument(:a, nil)

      # Assert
      assert argument.name == :a
    end
  end
end
