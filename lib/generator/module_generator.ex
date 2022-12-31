defmodule Generator.Module do
  @spec generate_module(String.t(), Config.Function.t()) :: List[String.t()]
  def generate_module(file_path, config) do
    %Config.Function{
      function_name: function_name,
      extensions: extensions,
      constants: constants
    } = config

    {_, ast} =
      file_path
      |> File.read!()
      |> Code.string_to_quoted()

    module =
      [generate_header(function_name)] ++
        [generate_extensions(extensions)] ++
        [""] ++
        generate_constants(constants) ++
        [""] ++
        Generator.Algorithm.generate_algorithm(ast, config) ++
        [""] ++
        [generate_footer(function_name)]

    module
  end

  @spec generate_header(String.t()) :: String.t()
  def generate_header(module_name) do
    header = "#{String.duplicate("-", 20)} MODULE #{module_name} #{String.duplicate("-", 20)}"
    header
  end

  @spec generate_footer(String.t()) :: String.t()
  def generate_footer(module_name) do
    length = 20 + 20 + 6 + 3 + String.length(module_name)
    footer = String.duplicate("=", length)
    footer
  end

  @spec generate_extensions(List[String.t()]) :: String.t()
  def generate_extensions(extensions) do
    if length(extensions) > 0 do
      "EXTENDS #{Enum.join(extensions, ", ")}"
    else
      ""
    end
  end

  @spec generate_constants(List[String.t()]) :: List[String.t()]
  def generate_constants(constants) do
    constants |> Enum.map(fn const -> "CONSTANT #{const}" end)
  end
end
