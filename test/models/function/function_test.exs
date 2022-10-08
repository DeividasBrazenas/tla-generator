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

      assert length(function.cases) == 2
      fn_case_1 =  Enum.at(function.cases, 0)
      assert fn_case_1.metadata != nil
      assert fn_case_1.actions != nil

      fn_case_2 =  Enum.at(function.cases, 1)
      assert fn_case_2.metadata != nil
      assert fn_case_2.actions != nil
    end
  end
end
