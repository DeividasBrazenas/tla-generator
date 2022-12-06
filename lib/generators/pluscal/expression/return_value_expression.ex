defmodule Generators.PlusCal.Expression.Return.Value do
  alias Models.Common.Indent, as: Indent

  @behaviour Generators.PlusCal.Expression

  @impl Generators.PlusCal.Expression
  @spec generate_expression(any(), List[Models.Argument.t()], Integer.t()) :: List[String.t()]
  def generate_expression(%Models.Expression.Return.Value{} = expression, fn_inputs, indent_level) do
    tla_string = to_tla_string(expression.value, fn_inputs)

    IO.inspect(tla_string)

    [
      "#{Indent.build(indent_level)}result_#{expression.function_name} := #{tla_string};",
    ]
  end

  @spec to_tla_string(Models.Argument.t(), List[Models.Argument.t()]) :: String.t()
  defp to_tla_string(%Models.Argument.Constant{} = argument, _fn_inputs) do
    Generators.Common.Constant.to_tla_constant(argument.value)
  end

  defp to_tla_string(%Models.Argument.Variable{} = argument, fn_inputs) do
    Generators.Common.Argument.get_accessor(argument.name, fn_inputs)
  end

  defp to_tla_string(%Models.Argument.Struct{} = argument, fn_inputs) do
    to_tla_string(argument.arguments, fn_inputs)
  end

  defp to_tla_string(%Models.Argument.Map{} = argument, fn_inputs) do
    case length(argument.key_value_pairs) do
      0 ->
        "{}"

      _ ->
        IO.inspect(fn_inputs)

        inner_arguments =
          argument.key_value_pairs
          |> Enum.map(fn {name, arg} ->
            "#{name} |-> #{to_tla_string(arg, fn_inputs)}"
          end)

        "[#{Enum.join(inner_arguments, ", ")}]"
    end
  end

  defp to_tla_string(%Models.Argument.Tuple{} = argument, fn_inputs) do
    inner_arguments =
      argument.arguments |> Enum.map(fn {_idx, arg} -> to_tla_string(arg, fn_inputs) end)

    "<<#{Enum.join(inner_arguments, ", ")}>>"
  end
end
