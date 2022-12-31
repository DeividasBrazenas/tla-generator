# See example: https://elixirforum.com/t/order-of-execution-of-on-definition-before-compile-and-after-compile/38465
defmodule Extractors.PlusCal do
  @tla2tools_path "C:/TLA+/toolbox/tla2tools.jar"

  defmacro __using__(_opts) do
    quote do
      # Module.register_attribute(__MODULE__, :tlagen_function, accumulate: true, persist: true)

      @after_compile Extractors.PlusCal
    end
  end

  def __after_compile__(_env, bytecode) do
    # Gets debug_info chunk from BEAM file
    chunks =
      case :beam_lib.chunks(bytecode, [:debug_info]) do
        {:ok, {_mod, chunks}} -> chunks
        {:error, _, error} -> throw("Error: #{inspect(error)}")
      end

    # Gets the (extended) Elixir abstract syntax tree from debug_info chunk
    dbgi_map =
      case chunks[:debug_info] do
        {:debug_info_v1, :elixir_erl, metadata} ->
          case metadata do
            {:elixir_v1, map, _} ->
              # Erlang extended AST available
              map
          end

        x ->
          throw("Error: #{inspect(x)}")
      end

    file_path = Map.get(dbgi_map, :file)

    regex_matches = Regex.run(~r/^(.+)\/([^\/]+)\.ex$/, file_path)
    directory = Enum.at(regex_matches, 1)
    file_name = Enum.at(regex_matches, 2)

    config_path = Path.join(directory, "#{file_name}.tlagen.json")
    config = Config.Module.get_config(config_path)

    %Config.Module{functions: functions} = config

    result_directory_base = Path.join(directory, "#{file_name}_specs")

    functions
    |> Enum.map(fn function ->
      module_lines = Generator.Module.generate_module(file_path, function)

      file_name = "#{function.function_name}.tla"
      result_directory = Path.join("#{result_directory_base}", function.function_name)
      result_path = Path.join(result_directory, file_name)

      File.mkdir_p!(Path.dirname(result_path))
      File.write!(result_path, Enum.join(module_lines, "\n"))

      IO.puts("----- Generating TLA+ for #{file_name} -----")

      System.cmd("java", ["-cp", @tla2tools_path, "pcal.trans", file_name],
        cd: result_directory,
        into: IO.stream()
      )

      IO.puts("----- Running model checking for #{file_name} -----")

      System.cmd("java", ["-cp", @tla2tools_path, "tlc2.TLC", file_name],
        cd: result_directory,
        into: IO.stream()
      )

      :timer.sleep(1000)

      ref_file_name = "#{function.function_name}_REF.tla"
      IO.puts("----- Running model checking for #{ref_file_name} -----")

      System.cmd("java", ["-cp", "tla2tools.jar", "tlc2.TLC", ref_file_name],
        cd: result_directory,
        into: IO.stream()
      )
    end)
  end
end
