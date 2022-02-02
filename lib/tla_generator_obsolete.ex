defmodule TlaGeneratorObsolete do
  # Object for holding definition of one function
  @type func_definition :: %{
          name: String,
          arguments: List[string],
          body: List[string]
        }

  # Entry point for generating TLA+ specification
  def generate(input_file_path, output_file_path) do
    {:ok, ast} =
      input_file_path
      |> Path.expand()
      |> File.read!()
      |> Code.string_to_quoted()

    moduleName = getModuleName(ast)

    {_, definitions} = Macro.postwalk(ast, [], &getDefinitions/2)

    tla =
      tlaModuleBeginning(moduleName)
      |> tlaDefinitions(definitions)
      |> tlaModuleEnding()

    output_file_path
    |> Path.expand()
    |> File.write!(Enum.join(tla, "\n"))

    :ok
  end

  defp getModuleName({:defmodule, _, [{:__aliases__, _, [name]}, _]}) do
    name
  end

  # Returns definitions of functions
  defp getDefinitions(
         {:def, _, [{function, _, args}, body]} = node,
         acc
       ) do
    {_, arguments} = Macro.postwalk(args, [], &getArguments/2)
    {_, body} = Macro.postwalk(body, [], &getBody/2)

    func_definition = %{
      name: function,
      arguments: arguments,
      body: body
    }

    {node, acc ++ [func_definition]}
  end
  defp getDefinitions(node, acc), do: {node, acc}

  defp getArguments(
         {argument, _, _} = node,
         acc
       ) do
    {node, acc ++ [argument]}
  end

  defp getArguments(node, acc), do: {node, acc}

  defp getBody({:if, _, args} = node, _) do
    condition = getCondition(List.first(args))
    body = getBody(List.last(args))
    {node, [condition] ++ body}
  end

  defp getBody(node, acc), do: {node, acc}

  defp getBody(do: {ifTrue, _, _}, else: {ifFalse, _, _}) do
    ["    THEN #{ifTrue}", "    ELSE #{ifFalse}"]
  end

  defp getCondition({operator, _, [{left, _, _}, {right, _, _}]}) do
    tlaOperator = getTlaOperator(operator)
    "IF #{left} #{tlaOperator} #{right}"
  end

  defp getCondition(node), do: {node}

  defp tlaModuleBeginning(name) do
    tlaValue = "------------------------------ MODULE #{name} ------------------------------"
    [tlaValue]
  end

  defp tlaModuleEnding(tla) do
    length = String.length(List.first(tla))
    tlaValue = String.duplicate("=", length)
    tla ++ [tlaValue]
  end

  defp tlaDefinitions(tla, definitions) do
    defsLines = Enum.map(definitions, fn def -> tlaDefinition(def) end)
    tlaValue = Enum.join(defsLines, "\n")
    tla ++ [tlaValue]
  end

  defp tlaDefinition(definition) do
    lines = ["#{definition.name}(#{Enum.join(definition.arguments, ", ")}) ==\n"]
    bodyLines = Enum.map(definition.body, fn bodyLine -> "  #{bodyLine}\n" end)
    lines ++ bodyLines
  end

  defp getTlaOperator(operator) do
    cond do
      operator == :< -> "<"
      operator == :> -> ">"
      operator == :<= -> "\\leq"
      operator == :>= -> "\\geq"
      operator == :== -> "="
    end
  end
end
