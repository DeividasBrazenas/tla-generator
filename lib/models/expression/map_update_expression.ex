defmodule Models.Expression.Map.Update do
  @moduledoc """
  Defines `value update` expression
  """
  @behaviour Models.Expression

  use TypedStruct

  typedstruct do
    field(:variable_name, atom(), default: nil, enforce: true)
    field(:variable_to_update_name, atom(), default: nil, enforce: true)
    field(:updated_key_value_pairs, List[{atom(), any()}], default: [], enforce: true)
  end

  @impl Models.Expression
  @spec parse_expression(any(), Models.Function.Clause.Metadata.t()) :: Models.Expression.Map.Update.t()
  def parse_expression(
        {:=, _,
         [
           {variable_name, _, _},
           {_, _, [{:|, _, [{variable_to_update_name, _, _}, updated_key_value_pairs_ast]}]}
         ]},
        _metadata
      ) do
    updated_key_value_pairs =
      updated_key_value_pairs_ast
      |> Enum.map(fn {key, ast} -> get_updated_key_value_pair(key, ast) end)

    expression = %Models.Expression.Map.Update{
      variable_name: variable_name,
      variable_to_update_name: variable_to_update_name,
      updated_key_value_pairs: updated_key_value_pairs
    }

    expression
  end

  @spec get_updated_key_value_pair(atom(), any()) :: {atom(), atom()}
  defp get_updated_key_value_pair(key, {value, _, nil}) do
    {key, value}
  end

  defp get_updated_key_value_pair(key, value) do
    {key, value}
  end
end
