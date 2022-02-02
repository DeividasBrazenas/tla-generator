defmodule FunctionSpecExtractor do
  @spec extractSpecs(any) :: List[FunctionSpecModel]
  def extractSpecs(ast) do
    {_, specs} = Macro.postwalk(ast, [], &getSpec/2)
    specs
  end

  defp getSpec(
         {:spec, _, [{:"::", _, [{method, _, argumentsList}, {returnType, _, _}]}]} = node,
         acc
       ) do
        functionSpec = %FunctionSpecModel{
      name: method,
      argumentTypes: Enum.map(argumentsList, fn {argumentType, _, _} -> argumentType end),
      returnType: returnType
    }

    {node, acc ++ [functionSpec]}
  end

  defp getSpec(node, acc), do: {node, acc}
end
