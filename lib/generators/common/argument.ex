defmodule Generators.Common.Argument do
  # Returns arguments from a clause that has all arguments
  @spec get_arguments(List[Models.Function.Clause.t()]) :: List[atom()]
  def get_arguments(clauses) do
    clause_with_all_arguments =
      clauses
      |> Enum.filter(fn c -> !Enum.any?(c.metadata.arguments, fn arg -> arg === :_ end) end)
      |> Enum.at(0)

    clause_with_all_arguments.metadata.arguments
  end

  @spec get_argument_names(Models.Function.t(), String.t()) :: List[String.t()]
  def get_argument_names(function, prefix) do
    arguments_count = length(function.spec.argument_types)
    {_, func_argument_names} =
      Enum.to_list(1..arguments_count)
      |> Enum.map_reduce([], fn arg_number, acc ->
        argument_name = get_argument_name(function.clauses, arg_number)
        {arg_number, acc ++ ["#{prefix}#{argument_name}"]}
      end)

    func_argument_names
  end

  @spec get_argument_name(List[Models.Function.Clause.t()], Integer.t()) :: String.t()
  def get_argument_name(clauses, argument_index) do
    {_, name} =
      clauses
      |> Enum.map_reduce(nil, fn clause, _ ->
        argument = Enum.at(clause.metadata.arguments, argument_index - 1)

        argument_name = argument.name

        if argument_name != nil and
             !String.starts_with?(Atom.to_string(argument_name), "_") do
          {clause, argument_name}
        else
          {clause, nil}
        end
      end)

    if name != nil do
      name
    else
      "arg_#{argument_index}"
    end
  end
end
