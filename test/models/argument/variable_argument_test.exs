defmodule Models.Type.Variable.Tests do
  use ExUnit.Case
  doctest Models.Type.Variable

  describe "variable argument" do
    test "is parsed" do
      # Act
      argument = Models.Type.Variable.parse_type(:a, nil)

      # Assert
      assert argument.name == :a
    end
  end
end
