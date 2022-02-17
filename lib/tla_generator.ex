defmodule Tla.Generator do
  def generate(module_name, input_file_path) do
    {_, ast} =
      input_file_path
      |> File.read!()
      |> Code.string_to_quoted()

    tla =
      [getHeader(module_name)] ++
        Tla.Generator.Body.get(ast) ++
        [getFooter(module_name)]

    Enum.join(tla, "\n")
  end

  @spec getHeader(String.t()) :: String.t()
  def getHeader(module_name) do
    tlaValue = "#{String.duplicate("-", 33)} MODULE #{module_name} #{String.duplicate("-", 33)}"
    tlaValue
  end

  @spec getFooter(String.t()) :: String.t()
  defp getFooter(module_name) do
    length = 33 + 33 + 6 + 3 + String.length(module_name)
    String.duplicate("=", length)
  end
end