# See example: https://elixirforum.com/t/order-of-execution-of-on-definition-before-compile-and-after-compile/38465
defmodule Tla.Extractor do
  defmacro __using__(_opts) do
    # IO.puts("Tla.Extractor __using__")

    quote do
      Module.register_attribute(__MODULE__, :tla_generation_type, accumulate: true, persist: true)
      Module.register_attribute(__MODULE__, :tla_generation_defs, accumulate: true, persist: true)
      # @on_definition Tla.Extractor
      # @before_compile Tla.Extractor
      @after_compile Tla.Extractor
    end
  end

  # def __on_definition__(env, kind, name, args, guards, body) do
  #   IO.puts(
  #     "Tla.Extractor __on_definition__ #{kind}: #{name}(#{inspect(args)}) with #{inspect(guards)} = #{inspect(body)}"
  #   )

  #   tla_generation_type = Module.get_attribute(env.module, :tla_generation_type, [])
  #   Module.put_attribute(env.module, :tla_generation_type, [{name, args, guards, body} | tla_generation_type])
  # end

  # def __before_compile__(env) do
  #   Enum.each(Map.keys(env), fn k ->
  #     IO.puts(
  #       "Tla.Extractor __before_compile__, env.#{inspect(k)}=#{inspect(Map.get(env, k), pretty: true, limit: :infinity, printable_limit: :infinity)}"
  #     )
  #   end)
  # end

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

    # IO.puts("Tla.Extractor __after_compile__, #{inspect(dbgi_map[:attributes], pretty: true)}")

    module_name = inspect(dbgi_map[:module])
    file_path = String.replace(inspect(dbgi_map[:file]), "\"", "")

    attributes = dbgi_map[:attributes]

    # Only first generation type from module will be used
    is_generation_type_defined = Keyword.has_key?(attributes, :tla_generation_type)
    tla_generation_defs = Keyword.get_values(attributes, :tla_generation_defs)

    # For TLA to be generated, generation type and defs to generate should be defined
    if is_generation_type_defined and Enum.any?(tla_generation_defs) do
      tla_generation_type = Keyword.fetch!(attributes, :tla_generation_type)

      result = Tla.Generator.generate(module_name, file_path, tla_generation_type, tla_generation_defs)

      result_path =
        String.replace(
          String.replace(inspect(dbgi_map[:file]), "\"", ""),
          String.replace(inspect(dbgi_map[:relative_file]), "\"", ""),
          ""
        )
        |> Path.join("priv")
        |> Path.join("#{module_name}.tla")

      File.mkdir_p!(Path.dirname(result_path))
      File.write!(result_path, result)
      IO.puts(result)
    end
  end
end
