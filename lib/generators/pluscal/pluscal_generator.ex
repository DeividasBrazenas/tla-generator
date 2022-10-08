defmodule Generators.PlusCal do
  @spec generate_module(String.t(), String.t(), List[atom()]) :: List[String.t()]
  def generate_module(module_name, input_file_path, generation_defs) do
    {_, ast} =
      input_file_path
      |> File.read!()
      |> Code.string_to_quoted()

    specs = Models.Function.Spec.parse_specs(generation_defs, ast)
    functions = Models.Function.parse_functions(specs, ast)

    module_lines =
      [Generators.PlusCal.Module.Metadata.generate_header(module_name)] ++
        [Generators.PlusCal.Module.Metadata.generate_extensions()] ++
        [Generators.PlusCal.Module.Metadata.generate_constants(functions)] ++
        [""] ++
        Generators.PlusCal.Algorithm.generate_algorithm(module_name, functions) ++
        [Generators.PlusCal.Module.Metadata.generate_footer(module_name)]

    IO.inspect(module_lines)
    Enum.join(module_lines, "\n")
  end
end
