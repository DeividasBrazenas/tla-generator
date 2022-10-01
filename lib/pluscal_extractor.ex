# See example: https://elixirforum.com/t/order-of-execution-of-on-definition-before-compile-and-after-compile/38465
defmodule PlusCal.Extractor do
  @tla2tools_path "C:/TLA+/toolbox/tla2tools.jar"

  defmacro __using__(_opts) do
    quote do
      Module.register_attribute(__MODULE__, :tla_generation_defs, accumulate: true, persist: true)
      @after_compile PlusCal.Extractor
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


    module_name = inspect(dbgi_map[:module])
    file_path = String.replace(inspect(dbgi_map[:file]), "\"", "")

    attributes = dbgi_map[:attributes]

    tla_generation_defs = Keyword.get_values(attributes, :tla_generation_defs)
    IO.inspect(tla_generation_defs)
    # For TLA to be generated, generation type and defs to generate should be defined
    result = PlusCal.Generator.generate(module_name, file_path, tla_generation_defs)

    file_name = "#{module_name}.tla"
    result_folder =
      String.replace(
        String.replace(inspect(dbgi_map[:file]), "\"", ""),
        String.replace(inspect(dbgi_map[:relative_file]), "\"", ""),
        ""
      )
      |> Path.join("priv")

    result_path =
      result_folder
      |> Path.join(file_name)

    File.mkdir_p!(Path.dirname(result_path))
    File.write!(result_path, result)

    # Generate TLA+ from PlusCal
    System.cmd("java", ["-cp", @tla2tools_path, "pcal.trans", file_name], cd: result_folder)

    # Remove old PlusCal file
    File.rm_rf!(result_folder |> Path.join("#{module_name}.old"))
  end
end
