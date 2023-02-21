defmodule Bracha.Test do
  use ExUnit.Case

  test "bracha" do
    dir = File.cwd!() |> Path.join("test/apps/bracha/lib")

    config = Config.Module.get_config(Path.join(dir, "rbc_bracha.tlagen.json"))

    %Config.Module{functions: functions} = config

    function = Enum.at(functions, 0)

    module =
      Generator.Module.generate_module(
        Path.join(dir, "rbc_bracha.ex"),
        function
      )

    IO.inspect(module)
    result_path =
      File.cwd!() |> Path.join("test/tlagen/priv/#{function.function_name}.tla")

    File.mkdir_p!(Path.dirname(result_path))
    File.write!(result_path, Enum.join(module, "\n"))
  end
end
