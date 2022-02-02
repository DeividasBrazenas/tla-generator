defmodule TlaGeneratorTest do
  use ExUnit.Case
  doctest TlaGenerator

  test "debug" do
    result =
      TlaGenerator.generate("Max", "c:/University/Master's Thesis/tla-generator/lib/max.ex")
      IO.puts(result)
  end

  # test "debug" do
  #   TlaGenerator.generate(
  #     "C:\\University\\Master's Thesis\\tla-generator\\lib\\max.ex",
  #     "C:\\University\\Master's Thesis\\tla-generator\\generated\\max.tla"
  #   )
  # end
end
