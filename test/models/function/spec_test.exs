defmodule Models.Function.Spec.Tests do
  use ExUnit.Case
  doctest Models.Function.Spec

  describe "spec" do
    test "is parsed" do
      # Arrange
      file_name = "max.ex"
      generation_defs = [:max]
      input_file_path = File.cwd!() |> Path.join("test/apps/math/lib") |> Path.join(file_name)

      {_, ast} =
        input_file_path
        |> File.read!()
        |> Code.string_to_quoted()

      # Act
      specs = Models.Function.Spec.parse_specs(generation_defs, ast)

      # Assert
      assert length(specs) == 1

      spec = List.first(specs)
      assert spec.name == :max
      assert spec.argument_types == [:integer, :integer]
      assert spec.return_type == :integer
    end
  end
end
