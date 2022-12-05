defmodule Generators.PlusCal.Test do
  use ExUnit.Case
  doctest Generators.PlusCal

  describe "generator" do
    # test "generates min" do
    #   module_name = "Min"
    #   file_name = "min.ex"
    #   generation_defs = [:min]

    #   source_path = File.cwd!() |> Path.join("test/apps/math/lib") |> Path.join(file_name)

    #   result = Generators.PlusCal.generate_module(module_name, source_path, generation_defs, [])
    # end

    # test "generates max" do
    #   module_name = "Max"
    #   file_name = "max.ex"
    #   generation_defs = [:max_v2]

    #   source_path = File.cwd!() |> Path.join("test/apps/math/lib") |> Path.join(file_name)

    #   result = Generators.PlusCal.generate_module(module_name, source_path, generation_defs, [])
    # end

    # @tag :run
    # test "generates math" do
    #   module_name = "Math"
    #   file_name = "math.ex"
    #   generation_defs = [:compare_v2]
    #   source_path = File.cwd!() |> Path.join("test/apps/math/lib") |> Path.join(file_name, [])

    #   {_, ast} =
    #     source_path
    #     |> File.read!()
    #     |> Code.string_to_quoted()

    #   IO.inspect(ast)
    #   result = Generators.PlusCal.generate_module(module_name, source_path, generation_defs, [])
    # end

    @tag :run
    test "generates rbc" do
      module_name = "Rbc"
      file_name = "rbc_cachin_tessaro.ex"
      pluscal_procedures = [:handle_new, :handle_input]
      pluscal_macros = [:broadcast_val, :rs_encode, :hash]
      source_path = File.cwd!() |> Path.join("test/apps/wasper/lib/wasper_hbbft") |> Path.join(file_name)

      {_, ast} =
        source_path
        |> File.read!()
        |> Code.string_to_quoted()

      result = Generators.PlusCal.generate_module(module_name, source_path, pluscal_procedures, pluscal_macros)

      result_path = File.cwd!() |> Path.join("test/generator/pluscal/priv/rbc.tla")
      File.mkdir_p!(Path.dirname(result_path))
      File.write!(result_path, result)
    end

    # test "generates gcd" do
    #   module_name = "Gcd"
    #   file_name = "gcd.ex"
    #   generation_defs = [:gcd]

    #   source_path = File.cwd!() |> Path.join("test/apps/math/lib") |> Path.join(file_name)

    #   result = Generators.PlusCal.generate_module(module_name, source_path, generation_defs, [])
    # end

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
