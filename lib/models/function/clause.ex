defmodule Models.Function.Clause do
  @moduledoc """
  Module defining the single function's clause
  """
  use TypedStruct

  typedstruct do
    field(:metadata, Models.Function.Clause.Metadata.t(), default: nil)
    field(:expressions, List[Models.Expression.t()], default: [])
  end

  @spec parse_clause(Models.Function.Clause.Metadata.t(), any()) :: Models.Function.Clause.t()
  def parse_clause(metadata, body_ast) do
    fn_clause = %Models.Function.Clause{
      metadata: metadata,
      expressions: Models.Expression.parse_expressions(body_ast, metadata)
    }

    fn_clause
  end

  @spec get_defined_variables(Models.Function.Clause.t()) :: List[String.t()]
  def get_defined_variables(clause = %Models.Function.Clause{}) do
    {_, defined_variables} =
      clause.expressions
      |> Enum.flat_map(fn expr ->
        case expr do
          %Models.Expression.Map.Update{} -> [expr.variable_name]
          %Models.Expression.Call.Function{} -> [expr.variable_name]
          _ -> []
        end
      end)
      |> Enum.map_reduce([], fn var, acc ->
        is_input_arg = Models.Argument.is_input_argument(var, clause.metadata.arguments)
        IO.inspect(is_input_arg)

        case is_input_arg do
          true -> {var, acc}
          false -> {var, acc ++ [var]}
        end
      end)

    IO.inspect(defined_variables)
    defined_variables |> Enum.uniq()
  end
end
