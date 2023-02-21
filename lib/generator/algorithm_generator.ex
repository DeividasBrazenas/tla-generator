defmodule Generator.Algorithm do
  alias Common.Indent, as: Indent

  @spec generate_algorithm(any(), Config.Function.t()) :: List[String.t()]
  def generate_algorithm(ast, config) do
    %Config.Function{
      function_name: function_name,
      global_variables: global_variables,
      definitions: predefined_definitions
    } = config

    {process_lines, generated_definitions} = Generator.Process.generate_process(ast, config)

    algorithm =
      [generate_header(function_name)] ++
        generate_global_variables(global_variables) ++
        [""] ++
        generate_definitions(predefined_definitions, generated_definitions) ++
        [""] ++
        process_lines ++
        [generate_footer()]

    algorithm
  end

  @spec generate_header(String.t()) :: String.t()
  def generate_header(module_name) do
    header = "(*--algorithm #{module_name}"
    header
  end

  @spec generate_footer() :: String.t()
  def generate_footer() do
    footer = "end algorithm; *)"
    footer
  end

  @spec generate_global_variables(List[Config.Variable.t()]) :: List[String.t()]
  def generate_global_variables(variables) do
    ["variables"] ++
      Enum.flat_map(variables, fn %Config.Variable{name: name, assignment_lines: assignment_lines} ->
        case length(assignment_lines) do
          1 ->
            ["#{Indent.build(1)}#{name} #{Enum.at(assignment_lines, 0)},"]

          _ ->
            ["#{Indent.build(1)}#{name} #{Enum.at(assignment_lines, 0)}"] ++
              (assignment_lines
               |> Enum.slice(1..-2)
               |> Enum.map(fn assignment_line ->
                 "#{Indent.build(3)} #{assignment_line}"
               end)) ++
              ["#{Indent.build(3)} #{Enum.at(assignment_lines, -1)},"]
        end
      end)
  end

  @spec generate_definitions(List[String.t()], List[String.t()]) :: List[String.t()]
  def generate_definitions(predefined_definitions, generated_definitions) do
    ["define"] ++
      Enum.map(predefined_definitions ++ generated_definitions, fn definition ->
        "#{Indent.build(1)}#{definition}"
      end) ++
      ["end define;"]
  end
end
