defmodule TlaGeneratorTest do
  use ExUnit.Case
  doctest TlaGenerator

  test "debug" do
    TlaGenerator.generate(
      "C:\\University\\Master's Thesis\\tla-generator\\lib\\math.ex",
      "C:\\University\\Master's Thesis\\tla-generator\\tla\\Math.tla"
    )
  end
end
