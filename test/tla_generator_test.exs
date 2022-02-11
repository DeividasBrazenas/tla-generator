defmodule Tla.GeneratorTest do
  use ExUnit.Case
  doctest Tla.Generator

  test "debug" do
    module_name = "Math"
    file_name = "math.ex"

    source = File.cwd!() |> Path.join("elixir_sources") |> Path.join(file_name)

    result = Tla.Generator.generate(module_name, source)

    IO.puts(result)
  end
end
