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
    "#{condition.left_operand} #{Generators.Common.Argument.get_pluscal_operator(condition.operator)} #{condition.right_operand}"
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

    conditions = Generators.Common.Argument.generate_tla_string(argument_with_constant, prefix, "")

    conditions
  end
end
