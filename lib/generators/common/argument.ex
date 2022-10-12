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
end
