defmodule Models.Function.Tests do
  use ExUnit.Case
  doctest Models.Function

  describe "function" do
    test "max is parsed" do
      # Arrange
      file_name = "max.ex"
      generation_defs = [:max]
      input_file_path = File.cwd!() |> Path.join("test/apps/math/lib") |> Path.join(file_name)

      {_, ast} =
        input_file_path
        |> File.read!()
        |> Code.string_to_quoted()

      specs = Models.Function.Spec.parse_specs(generation_defs, ast)

      # Act
      functions = Models.Function.parse_functions(specs, ast)

      assert length(functions) == 1

      function = Enum.at(functions, 0)
      assert function.spec != nil

      assert length(function.clauses) == 2
      fn_clause_1 =  Enum.at(function.clauses, 0)
      assert fn_clause_1.metadata != nil
      assert fn_clause_1.expressions != nil

      fn_clause_2 =  Enum.at(function.clauses, 1)
      assert fn_clause_2.metadata != nil
      assert fn_clause_2.expressions != nil
    end
  end
end
