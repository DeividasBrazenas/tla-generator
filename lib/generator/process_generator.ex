defmodule Generator.Process do
  alias Common.Indent

  @spec generate_process(any(), Config.Function.t()) :: {List[String.t()], List[String.t()]}
  def generate_process(ast, config) do
    %Config.Function{
      function_name: function_name,
      global_variables: global_variables,
      local_variables: predefined_local_variables,
      process: process
    } = config

    module_body = get_module_body(ast)
    function_ast = get_function_ast(function_name, module_body)

    {lines, generated_local_variables, generated_definitions} =
      Generator.Expressions.generate_process_expressions(function_ast, 1)

    {[generate_header(process)] ++
       generate_variables(predefined_local_variables, generated_local_variables, global_variables) ++
       ["begin"] ++
       ["#{function_name}:"] ++
       lines ++
       [generate_footer()], generated_definitions}
  end

  @spec get_module_body(any()) :: List[Tuple.t()]
  defp get_module_body(ast) do
    {_, body} =
      Macro.prewalk(ast, [], fn node, acc ->
        if acc == [] do
          new_acc =
            case node do
              {:__block__, _, body_ast} -> body_ast
              _ -> []
            end

          {node, new_acc}
        else
          {node, acc}
        end
      end)

    body
  end

  @spec get_function_ast(String.t(), List[Tuple.t()]) :: Tuple.t()
  defp get_function_ast(function_name, body_ast) do
    function_name_atom = String.to_atom(function_name)

    tlagen_idx =
      body_ast
      |> Enum.with_index(fn line, idx ->
        case line do
          {:@, _, [{:tlagen_function, _, [^function_name_atom]}]} -> idx
          _ -> nil
        end
      end)
      |> Enum.filter(fn idx -> idx != nil end)
      |> List.first(nil)

    case tlagen_idx do
      nil ->
        nil

      _ ->
        # Won't work if there are several function clauses
        function_ast_idx = tlagen_idx + 1
        Enum.at(body_ast, function_ast_idx)
    end
  end

  @spec generate_variables(List[Config.Variable.t()], List[String.t()], List[Config.Variable.t()]) :: List[String.t()]
  defp generate_variables(predefined_local_variables, generated_local_variables, global_variables) do
    global_variable_names =
      global_variables |> Enum.map(fn %Config.Variable{name: name} -> name end)

    ["variables"] ++
      Enum.map(predefined_local_variables, fn %Config.Variable{
                                                name: name,
                                                assignment_lines: assignment_lines
                                              } ->
        "#{Indent.build(1)}#{name} #{Enum.at(assignment_lines, 0)},"
      end) ++
      Enum.map(generated_local_variables -- global_variable_names, fn var ->
        cond do
          String.contains?(var, "=") -> "#{Indent.build(1)}#{var},"
          true -> "#{Indent.build(1)}#{var} = NULL,"
        end
      end)
  end

  @spec generate_header(String.t()) :: String.t()
  defp generate_header(process) do
    "fair process #{process}"
  end

  @spec generate_footer() :: String.t()
  defp generate_footer() do
    footer = "end process;"
    footer
  end
end
