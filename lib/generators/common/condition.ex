defmodule Generators.Common.Condition do
  # Returns TLA+ condition string
  @spec generate_conditions(Models.Common.Condition.t(), List[Models.Argument.t()]) ::
          List[String.t()]
  def generate_conditions(clause_condition, arguments_with_constant) do
    generated_clause_condition = generate_clause_condition(clause_condition)

    generated_arguments_condition =
      generate_arguments_condition(arguments_with_constant, generated_clause_condition != nil)

    if generated_clause_condition != nil do
      [generated_clause_condition] ++ generated_arguments_condition
    else
      generated_arguments_condition
    end
  end

  @spec generate_clause_condition(Models.Common.Condition.t()) :: String.t()
  def generate_clause_condition(nil), do: nil

  def generate_clause_condition(condition) do
    "#{condition.left_operand} #{get_pluscal_operator(condition.operator)} #{condition.right_operand}"
  end

  @spec generate_arguments_condition(List[Models.Argument.t()], boolean()) :: List[String.t()]
  def generate_arguments_condition([], _), do: []

  def generate_arguments_condition(arguments_with_constant, is_first_condition) do
    argument_conditions =
      arguments_with_constant
      |> Enum.with_index(fn argument, idx ->
        generate_argument_conditions(argument, idx, is_first_condition)
      end)
      |> Enum.flat_map(fn a -> a end)

    argument_conditions
  end

  @spec generate_argument_conditions(Models.Argument.t(), Integer.t(), boolean()) ::
          List[String.t()]
  defp generate_argument_conditions(argument_with_constant, index, is_first_condition) do
    prefix =
      case {index, is_first_condition} do
        {0, false} -> ""
        {_, _} -> "/\\ "
      end

    conditions = generate(argument_with_constant, prefix, "")

    conditions
  end

  @spec generate(Models.Argument.t(), String.t(), String.t()) :: List[String.t()]
  defp generate(argument = %Models.Argument.Constant{}, prefix, accessor) do
    ["#{prefix}#{accessor}#{argument.name} = #{get_constant_value(argument.value)}"]
  end

  defp generate(argument = %Models.Argument.Tuple{}, prefix, accessor) do
    generated =
      argument.arguments
      |> Enum.with_index(fn arg, idx ->
        generate(arg, prefix, "#{accessor}#{argument.name}[#{idx}]")
      end)
      |> Enum.flat_map(fn arg -> arg end)
      |> Enum.filter(fn arg -> arg != "" end)

    generated
  end

  defp generate(argument = %Models.Argument.Map{}, prefix, accessor) do
    generated =
      argument.key_value_pairs
      |> Enum.map(fn {key, arg} ->
        generate(arg, prefix, "#{accessor}#{argument.name}[\"#{key}\"]")
      end)
      |> Enum.flat_map(fn arg -> arg end)
      |> Enum.filter(fn arg -> arg != "" end)

    generated
  end

  defp generate(argument = %Models.Argument.Struct{}, prefix, accessor) do
    generated = generate(argument.arguments, prefix, "#{accessor}#{argument.name}")

    generated
  end

  defp generate(argument, _, _) do
    IO.inspect(argument)
    [""]
  end

  @spec get_constant_value(any()) :: String.t()
  defp get_constant_value(value) when is_atom(value) or is_binary(value), do: "\"#{value}\""
  defp get_constant_value(value) when is_number(value), do: value

  @spec get_pluscal_operator(atom()) :: String.t()
  defp get_pluscal_operator(operator) do
    case operator do
      :== -> " = "
      :!= -> " # "
      :< -> "<"
      :> -> ">"
      :<= -> "<="
      :>= -> ">="
    end
  end
end
