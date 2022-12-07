defmodule Generators.PlusCal.Expression.Map.Update do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Expression

  @impl Generators.PlusCal.Expression
  @spec generate_expression(any(), List[Models.Type.t()], List[atom()], Integer.t()) :: List[String.t()]
  def generate_expression(%Models.Expression.Map.Update{} = expression, fn_inputs, local_variables, indent_level) do
    lines =
      expression.updated_key_value_pairs
      |> Enum.with_index(fn {key, value}, idx ->
        left_side = "#{expression.variable_to_update_name}[\"#{key}\"]"

        is_variable_assignment = Generators.Common.Argument.get_accessor(value, fn_inputs, local_variables) != nil

        right_side =
          case is_variable_assignment do
            true -> "#{value}"
            false -> Generators.Common.Constant.to_tla_constant(value)
          end

        line = "#{left_side} := #{right_side}"

        cond do
          idx > 0 -> "#{Indent.build(indent_level)}|| #{line}"
          true -> "#{Indent.build(indent_level)}#{line}"
        end
      end)

    last_idx = length(expression.updated_key_value_pairs) - 1
    List.replace_at(lines, last_idx, "#{Enum.at(lines, last_idx)};") ++ [""]
  end
end
