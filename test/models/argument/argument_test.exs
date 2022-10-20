defmodule Models.Argument.Tests do
  use ExUnit.Case
  doctest Models.Argument

  describe "argument" do
    test "variable is parsed" do
      # Arrange
      ast = {:a, [line: 32], nil}

      # Act
      argument = Models.Argument.parse_argument(ast)

      # Assert
      assert argument.__struct__ == Models.Argument.Variable
    end

    test "tuple is parsed #1" do
      # Arrange
      ast = {:{}, [line: 1], [:<, {:a, [line: 1], nil}, {:b, [line: 1], nil}]}

      # Act
      argument = Models.Argument.parse_argument(ast)

      # Assert
      assert argument.__struct__ == Models.Argument.Tuple
    end

    test "tuple is parsed #2" do
      # Arrange
      ast = {{:a, [line: 1], nil}, {:b, [line: 1], nil}}

      # Act
      argument = Models.Argument.parse_argument(ast)

      # Assert
      assert argument.__struct__ == Models.Argument.Tuple
    end

    test "named tuple is parsed" do
      # Arrange
      ast = {:=, [line: 36], [{:named_tuple, [line: 36], nil}, {{:b, [line: 36], nil}, 7}]}

      # Act
      argument = Models.Argument.parse_argument(ast)

      # Assert
      assert argument.__struct__ == Models.Argument.Tuple
    end

    test "named struct is parsed" do
      # Arrange
      ast = {:=, [line: 1], [{:x, [line: 1], nil}, {:%, [line: 1], [{:__aliases__, [line: 1], [:Math]}, {:%{}, [line: 1], [operator: :<]}]}]}

      # Act
      argument = Models.Argument.parse_argument(ast)

      # Assert
      assert argument.__struct__ == Models.Argument.Struct
    end

    test "struct is parsed" do
      # Arrange
      ast = {:%, [line: 1], [{:__aliases__, [line: 1], [:Math]}, {:%{}, [line: 1], [operator: :<]}]}

      # Act
      argument = Models.Argument.parse_argument(ast)

      # Assert
      assert argument.__struct__ == Models.Argument.Struct
    end

    test "map is parsed" do
      # Arrange
      ast = {:%{}, [line: 1], [operator: :<]}

      # Act
      argument = Models.Argument.parse_argument(ast)

      # Assert
      assert argument.__struct__ == Models.Argument.Map
    end

    test "string is parsed as constant" do
      # Arrange
      ast = "a"

      # Act
      argument = Models.Argument.parse_argument(ast)

      # Assert
      assert argument.__struct__ == Models.Argument.Constant
    end

    test "atom is parsed as constant" do
      # Arrange
      ast = :a

      # Act
      argument = Models.Argument.parse_argument(ast)

      # Assert
      assert argument.__struct__ == Models.Argument.Constant
    end

    test "integer is parsed as constant" do
      # Arrange
      ast = 42

      # Act
      argument = Models.Argument.parse_argument(ast)

      # Assert
      assert argument.__struct__ == Models.Argument.Constant
    end

    test "float is parsed as constant" do
      # Arrange
      ast = 4.2

      # Act
      argument = Models.Argument.parse_argument(ast)

      # Assert
      assert argument.__struct__ == Models.Argument.Constant
    end
  end
end
