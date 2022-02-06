defmodule Tla.GeneratorTest do
  use ExUnit.Case
  doctest Tla.Generator

  test "debug" do
    result =
      Tla.Generator.generate(
        "Math",
        "c:/University/Master's Thesis/tla-generator/elixir_sources/math.ex"
      )

    IO.puts(result)
  end
end
