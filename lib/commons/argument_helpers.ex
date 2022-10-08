defmodule Commons.ArgumentHelpers do
  # Returns arguments from a case that has all arguments
  @spec get_arguments(List[Models.Function.Case.t()]) :: List[atom()]
  def get_arguments(cases) do
    case_with_all_arguments =
      cases
      |> Enum.filter(fn c -> !Enum.any?(c.metadata.arguments, fn arg -> arg === :_ end) end)
      |> Enum.at(0)

    case_with_all_arguments.metadata.arguments
  end
end
