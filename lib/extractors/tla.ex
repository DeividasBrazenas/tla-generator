# See example: https://elixirforum.com/t/order-of-execution-of-on-definition-before-compile-and-after-compile/38465
defmodule Extractors.TLA do
  defmacro __using__(_opts) do
    # IO.puts("Extractors.TLA __using__")

    quote do
      Module.register_attribute(__MODULE__, :tla_defs, accumulate: true, persist: true)
      # @on_definition Extractors.TLA
      # @before_compile Extractors.TLA
      @after_compile Extractors.TLA
    end
  end

  # def __on_definition__(env, kind, name, args, guards, body) do
  #   IO.puts(
  #     "Extractors.TLA __on_definition__ #{kind}: #{name}(#{inspect(args)}) with #{inspect(guards)} = #{inspect(body)}"
  #   )

  #   tla_defs = Module.get_attribute(env.module, :tla_defs, [])
  #   Module.put_attribute(env.module, :tla_defs, [{name, args, guards, body} | tla_defs])
  # end

  # def __before_compile__(env) do
  #   Enum.each(Map.keys(env), fn k ->
  #     IO.puts(
  #       "Extractors.TLA __before_compile__, env.#{inspect(k)}=#{inspect(Map.get(env, k), pretty: true, limit: :infinity, printable_limit: :infinity)}"
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

    # IO.puts("Extractors.TLA __after_compile__, #{inspect(dbgi_map[:attributes], pretty: true)}")

    moduleName = inspect(dbgi_map[:module])
    filePath = String.replace(inspect(dbgi_map[:file]), "\"", "")

    result = TLA.Generator.generate(moduleName, filePath)
    # IO.puts(result)
  end
end
