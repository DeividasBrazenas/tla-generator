defmodule Generators.PlusCal.Test do
  use ExUnit.Case
  doctest Generators.PlusCal

  describe "generator" do
    test "generates max" do
      module_name = "Max"
      file_name = "max.ex"
      generation_defs = [:max]

      source_path = File.cwd!() |> Path.join("test/apps/math/lib") |> Path.join(file_name)

      result = Generators.PlusCal.generate_module(module_name, source_path, generation_defs)
    end

    test "generates gcd" do
      module_name = "Gcd"
      file_name = "gcd.ex"
      generation_defs = [:gcd]

      source_path = File.cwd!() |> Path.join("test/apps/math/lib") |> Path.join(file_name)

      result = Generators.PlusCal.generate_module(module_name, source_path, generation_defs)
    end

    # test "apps/math" do
    #   File.rm_rf!("test/apps/math/priv")
    #   {_, 0} = System.cmd("mix", ["clean"], cd: "test/apps/math")
    #   {_, 0} = System.cmd("mix", ["compile"], cd: "test/apps/math")
    #   {_, 0} = System.cmd("tlapm", ["Math.tla"], cd: "test/apps/math/priv")
    #   {_, 0} = System.cmd("tlapm", ["Max.tla"], cd: "test/apps/math/priv")
    #   {_, 0} = System.cmd("tlapm", ["Min.tla"], cd: "test/apps/math/priv")
    #   {_, 0} = System.cmd("tlapm", ["Gcd.tla"], cd: "test/apps/math/priv")
    # end
  end
end
