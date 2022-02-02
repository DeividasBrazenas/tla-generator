defmodule TlaGenerator do
  def generate(moduleName, inputFilePath) do
    {_, ast} =
      inputFilePath
      |> File.read!()
      |> Code.string_to_quoted()

    tla =
      [TlaHeaderGenerator.getHeader(moduleName)] ++
        TlaBodyGenerator.getBody(ast) ++
        [TlaFooterGenerator.getFooter(moduleName)]

    Enum.join(tla, "\n")
  end
end
