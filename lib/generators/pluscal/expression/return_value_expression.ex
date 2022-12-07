defmodule Generators.PlusCal.Expression.Return.Value do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Expression

  @impl Generators.PlusCal.Expression
  @spec generate_expression(any(), List[Models.Type.t()], List[atom()], Integer.t()) ::
          List[String.t()]
  def generate_expression(
        %Models.Expression.Return.Value{} = expression,
        fn_inputs,
        local_variables,
        indent_level
      ) do
    IO.inspect(expression)
    tla_string = to_tla_string(expression.value, fn_inputs, local_variables)

    [
      "#{Indent.build(indent_level)}result_#{expression.parent_function_name} := #{tla_string};"
    ]
  end

  @spec to_tla_string(Models.Type.t(), List[Models.Type.t()], List[atom()]) :: String.t()
  defp to_tla_string(%Models.Type.Constant{} = argument, _fn_inputs, _local_variables) do
    Generators.Common.Constant.to_tla_constant(argument.value)
  end

  defp to_tla_string(%Models.Type.Variable{} = argument, fn_inputs, local_variables) do
    Generators.Common.Argument.get_accessor(argument.name, fn_inputs, local_variables)
  end

  defp to_tla_string(%Models.Type.Struct{} = argument, fn_inputs, local_variables) do
    to_tla_string(argument.arguments, fn_inputs, local_variables)
  end

  defp to_tla_string(%Models.Type.Map{} = argument, fn_inputs, local_variables) do
    case length(argument.key_value_pairs) do
      0 ->
        "{}"

      _ ->
        inner_arguments =
          argument.key_value_pairs
          |> Enum.map(fn {name, arg} ->
            "#{name} |-> #{to_tla_string(arg, fn_inputs, local_variables)}"
          end)

        "[#{Enum.join(inner_arguments, ", ")}]"
    end
  end

  defp to_tla_string(%Models.Type.Tuple{} = argument, fn_inputs, local_variables) do
    inner_arguments =
      argument.arguments
      |> Enum.map(fn {_idx, arg} -> to_tla_string(arg, fn_inputs, local_variables) end)

    "<<#{Enum.join(inner_arguments, ", ")}>>"
  end
end
