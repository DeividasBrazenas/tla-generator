defmodule Generators.PlusCal.Algorithm.Procedure.Expression.Map.Update do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Algorithm.Procedure.Expression

  @impl Generators.PlusCal.Algorithm.Procedure.Expression
  @spec generate_expression(any(), List[Models.Argument.t()], Integer.t()) :: List[String.t()]
  def generate_expression(%Models.Expression.Map.Update{} = expression, fn_inputs, indent_level) do
    lines =
      expression.updated_key_value_pairs
      |> Enum.with_index(fn {key, value}, idx ->
        left_side = "#{expression.variable_to_update_name}[\"#{key}\"]"

        is_variable_assignment = Generators.Common.Argument.get_accessor(value, fn_inputs) != nil

        right_side =
          case is_variable_assignment do
            true -> "#{value}"
            false -> Generators.Common.Constant.to_tla_constant(value)
          end

        line = "#{left_side} := #{right_side}"
        IO.inspect(line)

        cond do
          idx > 0 -> "#{Indent.build(indent_level)}|| #{line}"
          true -> "#{Indent.build(indent_level)}#{line}"
        end
      end)

    last_idx = length(expression.updated_key_value_pairs) - 1
    IO.inspect(last_idx)
    List.replace_at(lines, last_idx, "#{Enum.at(lines, last_idx)};")
  end
end
