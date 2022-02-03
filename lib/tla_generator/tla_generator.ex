defmodule TLA.Generator do
  def generate(moduleName, inputFilePath) do
    {_, ast} =
      inputFilePath
      |> File.read!()
      |> Code.string_to_quoted()

    tla =
      [TLA.Generator.Header.getHeader(moduleName)] ++
        TLA.Generator.Body.getBody(ast) ++
        [TLA.Generator.Footer.getFooter(moduleName)]

    Enum.join(tla, "\n")
  end
end
