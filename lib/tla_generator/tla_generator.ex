defmodule Tla.Generator do
  def generate(module_name, input_file_path) do
    {_, ast} =
      input_file_path
      |> File.read!()
      |> Code.string_to_quoted()

    tla =
      [Tla.Generator.Header.get(module_name)] ++
        Tla.Generator.Body.get(ast) ++
        [Tla.Generator.Footer.get(module_name)]

    Enum.join(tla, "\n")
  end
end
