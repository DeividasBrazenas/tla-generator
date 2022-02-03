defmodule TLA.GeneratorTest do
  use ExUnit.Case
  doctest TLA.Generator

  test "debug" do
    result =
      TLA.Generator.generate(
        "Math",
        "c:/University/Master's Thesis/tla-generator/elixir_sources/math.ex"
      )

    IO.puts(result)
  end
end
