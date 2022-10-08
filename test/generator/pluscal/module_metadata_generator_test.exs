defmodule Generators.PlusCal.Module.Metadata.Test do
  use ExUnit.Case
  doctest Generators.PlusCal.Module.Metadata

  describe "generate" do
    test "header" do
      # Arrange
      module_name = "Test"

      # Act
      header = Generators.PlusCal.Module.Metadata.generate_header(module_name)

      # Assert
      assert header == "------------------------------ MODULE Test ------------------------------"
    end

    test "footer" do
      # Arrange
      module_name = "Test"

      # Act
      footer = Generators.PlusCal.Module.Metadata.generate_footer(module_name)

      # Assert
      assert footer == "========================================================================="
    end
  end
end
