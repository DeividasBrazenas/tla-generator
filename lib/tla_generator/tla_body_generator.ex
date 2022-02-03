defmodule TlaBodyGenerator do
  def getBody(ast) do
    {_, generationType} = Macro.postwalk(ast, :not_specified, &getGenerationType/2)

    body =
      case generationType do
        :operation -> generateBodyByOperations(ast)
      end

    body
  end

  defp generateBodyByOperations(ast) do
    specs = FunctionSpecExtractor.extractSpecs(ast)
    functions = FunctionOperationBodyExtractor.extractFunctions(specs, ast)
    body = getTlaExtensions(specs) ++ getTlaFunctions(functions)
    body
  end

  defp getGenerationType({:tla_defs, _, [type]} = node, _) do
    {node, type}
  end

  defp getGenerationType(node, acc), do: {node, acc}

  @spec getTlaExtensions(List[FunctionSpecModel]) :: List[String]
  defp getTlaExtensions(functionSpecs) do
    extensions =
      Enum.map(functionSpecs, fn spec ->
        cond do
          spec.returnType === :integer -> "EXTENDS Naturals"
        end
      end)
      |> Enum.uniq()

    if length(extensions) > 0 do
      extensions ++ ["\n"]
    else
      extensions
    end
  end

  @spec getTlaFunctions(List[FunctionModel]) :: List[String]
  defp getTlaFunctions(functions) do
    tlaFunctions = Enum.reduce(functions, [], fn function, acc -> acc ++ getTlaFunction(function) end)

    tlaFunctions
  end

  defp getTlaFunction(%FunctionModel{spec: spec, arguments: arguments, cases: cases} = function) do
    functionDefinition = ["#{spec.name}(#{Enum.join(arguments, ", ")}) =="]

    functionBody =
      case function.cases > 1 do
        true ->
          ["  CHOOSE x #{getTlaVariableConstraints(spec.returnType)} :"] ++
            Enum.map(cases, fn {condition, return} ->
              "    \\/ (#{condition.left_operand} #{condition.operator} #{condition.right_operand}) /\\ x = #{return}"
            end)
      end

    functionDefinition ++ functionBody
  end

  @spec getTlaVariableConstraints(atom()) :: String
  defp getTlaVariableConstraints(type) do
    case type do
      :integer -> "\\in Nat"
    end
  end
end
