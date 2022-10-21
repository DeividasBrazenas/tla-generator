defmodule Generators.PlusCal.Module.Metadata do
  @spec generate_header(String.t()) :: String.t()
  def generate_header(module_name) do
    header = "#{String.duplicate("-", 30)} MODULE #{module_name} #{String.duplicate("-", 30)}"
    header
  end

  @spec generate_footer(String.t()) :: String.t()
  def generate_footer(module_name) do
    length = 30 + 30 + 6 + 3 + String.length(module_name)
    footer = String.duplicate("=", length)
    footer
  end

  @spec generate_extensions() :: String.t()
  def generate_extensions() do
    # For PlusCal
    extensions = ["Naturals"] ++ ["Sequences"]

    if length(extensions) > 0 do
      "EXTENDS #{Enum.join(extensions, ", ")}"
    else
      ""
    end
  end

  @spec generate_constants(List[Models.Function.t()]) :: String.t()
  def generate_constants(functions) do
    {_, input_arguments} =
      functions
      |> Enum.map_reduce([], fn func, acc ->
        func_argument_names = Generators.Common.Argument.get_argument_names(func, "in_")

        {func, acc ++ func_argument_names}
      end)

    if length(input_arguments) > 0 do
      "CONSTANTS #{Enum.join(input_arguments, ", ")}"
    else
      ""
    end
  end
end
