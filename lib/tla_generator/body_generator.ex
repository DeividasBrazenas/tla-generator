defmodule Tla.Generator.Body do
  @spec get(any) :: List[String.t()]
  def get(ast) do
    {_, _generation_type} = Macro.postwalk(ast, :not_specified, &get_generation_type/2)

    specs = Function.Spec.get(ast)
    functions = Function.Function.get(specs, ast)
    body = get_tla_extensions(specs) ++ get_tla_functions(functions)
    body
  end

  @spec(get_generation_type(any, atom()) :: any, atom())
  defp get_generation_type({:tla_defs, _, [type]} = node, _) do
    {node, type}
  end

  defp get_generation_type(node, acc), do: {node, acc}

  @spec get_tla_extensions(List[Function.Spec.t()]) :: List[String.t()]
  defp get_tla_extensions(specs) do
    extensions =
      Enum.map(specs, fn spec ->
        cond do
          spec.return_type === :integer -> "EXTENDS Naturals"
        end
      end)
      |> Enum.uniq()

    if length(extensions) > 0 do
      extensions ++ ["\n"]
    else
      extensions
    end
  end

  @spec get_tla_functions(List[Function.Function.t()]) :: List[String.t()]
  defp get_tla_functions(functions) do
    tla_functions =
      Enum.reduce(functions, [], fn function, acc -> acc ++ get_tla_function(function) end)

    tla_functions
  end

  @spec get_tla_function(Function.Function.t()) :: List[String.t()]
  defp get_tla_function(
         %Function.Function{spec: spec, arguments: arguments, cases: cases} = function
       ) do
    definition = ["#{spec.name}(#{Enum.join(arguments, ", ")}) =="]

    body =
      case function.cases > 1 do
        true ->
          ["  CHOOSE x #{get_tla_variable_constraints(spec.return_type)} :"] ++
            Enum.map(cases, fn fn_case ->
              "    \\/ (#{fn_case.condition.left_operand} #{fn_case.condition.operator} #{fn_case.condition.right_operand}) /\\ x = #{fn_case.return}"
            end)
      end

    definition ++ body ++ ["\n"]
  end

  @spec get_tla_variable_constraints(atom()) :: String.t()
  defp get_tla_variable_constraints(type) do
    case type do
      :integer -> "\\in Nat"
    end
  end
end
