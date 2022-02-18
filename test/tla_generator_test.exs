defmodule Tla.GeneratorTest do
  use ExUnit.Case
  doctest Tla.Generator

  # test "debug" do
  #   module_name = "Math"
  #   file_name = "math.ex"

  #   source = File.cwd!() |> Path.join("elixir_sources") |> Path.join(file_name)

  #   result = Tla.Generator.generate(module_name, source)

  #   IO.puts(result)
  # end

  test "apps/math" do
    File.rm_rf!("test/apps/math/priv/Math.tla")
    File.rm_rf!("test/apps/math/priv/Max.tla")
    File.rm_rf!("test/apps/math/priv/Min.tla")
    {_, 0} = System.cmd("mix", ["clean"], cd: "test/apps/math")
    {_, 0} = System.cmd("mix", ["compile"], cd: "test/apps/math")
    {_, 0} = System.cmd("tlapm", ["Math.tla"], cd: "test/apps/math/priv")
    {_, 0} = System.cmd("tlapm", ["Max.tla"], cd: "test/apps/math/priv")
    {_, 0} = System.cmd("tlapm", ["Min.tla"], cd: "test/apps/math/priv")
  end

end
