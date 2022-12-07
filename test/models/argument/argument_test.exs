defmodule Models.Type.Tests do
  use ExUnit.Case
  doctest Models.Type

  describe "argument" do
    test "variable is parsed" do
      # Arrange
      ast = {:a, [line: 32], nil}

      # Act
      argument = Models.Type.parse_type(ast)

      # Assert
      assert argument.__struct__ == Models.Type.Variable
    end

    test "tuple is parsed #1" do
      # Arrange
      ast = {:{}, [line: 1], [:<, {:a, [line: 1], nil}, {:b, [line: 1], nil}]}

      # Act
      argument = Models.Type.parse_type(ast)

      # Assert
      assert argument.__struct__ == Models.Type.Tuple
    end

    test "tuple is parsed #2" do
      # Arrange
      ast = {{:a, [line: 1], nil}, {:b, [line: 1], nil}}

      # Act
      argument = Models.Type.parse_type(ast)

      # Assert
      assert argument.__struct__ == Models.Type.Tuple
    end

    test "named tuple is parsed" do
      # Arrange
      ast = {:=, [line: 36], [{:named_tuple, [line: 36], nil}, {{:b, [line: 36], nil}, 7}]}

      # Act
      argument = Models.Type.parse_type(ast)

      # Assert
      assert argument.__struct__ == Models.Type.Tuple
    end

    test "named struct is parsed" do
      # Arrange
      ast = {:=, [line: 1], [{:x, [line: 1], nil}, {:%, [line: 1], [{:__aliases__, [line: 1], [:Math]}, {:%{}, [line: 1], [operator: :<]}]}]}

      # Act
      argument = Models.Type.parse_type(ast)

      # Assert
      assert argument.__struct__ == Models.Type.Struct
    end

    test "struct is parsed" do
      # Arrange
      ast = {:%, [line: 1], [{:__aliases__, [line: 1], [:Math]}, {:%{}, [line: 1], [operator: :<]}]}

      # Act
      argument = Models.Type.parse_type(ast)

      # Assert
      assert argument.__struct__ == Models.Type.Struct
    end

    test "map is parsed" do
      # Arrange
      ast = {:%{}, [line: 1], [operator: :<]}

      # Act
      argument = Models.Type.parse_type(ast)

      # Assert
      assert argument.__struct__ == Models.Type.Map
    end

    test "string is parsed as constant" do
      # Arrange
      ast = "a"

      # Act
      argument = Models.Type.parse_type(ast)

      # Assert
      assert argument.__struct__ == Models.Type.Constant
    end

    test "atom is parsed as constant" do
      # Arrange
      ast = :a

      # Act
      argument = Models.Type.parse_type(ast)

      # Assert
      assert argument.__struct__ == Models.Type.Constant
    end

    test "integer is parsed as constant" do
      # Arrange
      ast = 42

      # Act
      argument = Models.Type.parse_type(ast)

      # Assert
      assert argument.__struct__ == Models.Type.Constant
    end

    test "float is parsed as constant" do
      # Arrange
      ast = 4.2

      # Act
      argument = Models.Type.parse_type(ast)

      # Assert
      assert argument.__struct__ == Models.Type.Constant
    end
  end
end
