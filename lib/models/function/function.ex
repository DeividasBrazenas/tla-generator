defmodule Models.Function do
  @moduledoc """
  Module defining the function
  """
  use TypedStruct

  typedstruct do
    field(:spec, Models.Function.Spec.t(), default: nil)
    field(:clauses, List[Models.Function.Clause.t()], default: [])
  end

  @doc "Parses all functions of the AST"
  @spec parse_functions(List[Models.Function.Spec.t()], any()) :: List[Models.Function.t()]
  def parse_functions(specs, ast) do
    {_, all_definitions} = Macro.postwalk(ast, [], &get_function_definitions/2)

    IO.inspect(all_definitions)

    functions =
      specs
      |> Enum.map(fn spec ->
        function_definitions =
          all_definitions
          |> Enum.filter(fn {metadata, _} ->
            metadata.name === spec.name
          end)

        clauses =
          function_definitions
          |> Enum.map(fn {metadata, body_ast} ->
            Models.Function.Clause.parse_clause(metadata, body_ast)
          end)

        function = %Models.Function{
          spec: spec,
          clauses: clauses
        }

        function
      end)

    functions
  end

  # "Returns all defined functions"
  @spec get_function_definitions(any(), List[any()]) :: {any(), List[any()]}
  defp get_function_definitions({:defp, _, [metadata_ast, body_ast]} = node, acc) do
    IO.inspect(node)
    metadata = Models.Function.Clause.Metadata.parse_metadata(metadata_ast)
    {node, acc ++ [{metadata, body_ast}]}
  end

  defp get_function_definitions({:def, _, [metadata_ast, body_ast]} = node, acc) do
    IO.inspect(node)
    metadata = Models.Function.Clause.Metadata.parse_metadata(metadata_ast)
    {node, acc ++ [{metadata, body_ast}]}
  end

  defp get_function_definitions(node, acc), do: {node, acc}
end
