defmodule Generators.PlusCal.Algorithm.Macro do
  alias Models.Common.Indent, as: Indent

  @spec generate_macros(List[Models.Function.t()], List[atom()], Integer.t()) ::
          List[String.t()]
  def generate_macros(functions, pluscal_macros, indent_level) do
    macros =
      functions
      |> Enum.filter(fn function ->
        Enum.any?(pluscal_macros, fn macro_name ->
          macro_name == function.spec.name
        end)
      end)
      |> Enum.flat_map(fn function ->
        macro = generate_macro(function, indent_level)
        macro ++ [""]
      end)

    IO.inspect(macros)
    macros
  end

  @spec generate_macro(Models.Function.t(), Integer.t()) :: List[String.t()]
  defp generate_macro(function, indent_level) do
    IO.inspect(function)

    macro =
      [generate_header(function, indent_level)] ++
        ["#{Indent.build(indent_level)}begin"] ++
        [generate_footer(indent_level)]

    IO.inspect(macro)
    macro
  end

  @spec generate_header(Models.Function.t(), Integer.t()) :: String.t()
  defp generate_header(function, indent_level) do
    argument_names = Generators.Common.Argument.get_argument_names(function, "")

    "#{Indent.build(indent_level)}macro #{function.spec.name}(#{Enum.join(argument_names, ", ")})"
  end

  @spec generate_footer(Integer.t()) :: String.t()
  defp generate_footer(indent_level) do
    footer = "#{Indent.build(indent_level)}end macro;"
    footer
  end
end
