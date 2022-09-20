defmodule Tla.Generator.Models.Function.Case do
  use TypedStruct

  typedstruct do
    @typedoc "Type for a function case"

    field(:condition, Tla.Generator.Models.Function.Condition.t(), default: nil, enforce: true)
    field(:return, atom(), default: nil, enforce: true)
  end

  @spec get(List[Tla.Generator.Models.Function.Case.t()]) ::
          List[Tla.Generator.Models.Function.Case.t()]
  def get(cases) do
    ordered_cases =
      Enum.sort_by(cases, fn fn_case -> fn_case.condition end)
      |> Enum.reverse()
      |> Enum.reduce([], fn fn_case, acc ->
        if fn_case.condition != nil do
          acc ++ [fn_case]
        else
          previous_conditions = Enum.map(acc, fn fn_case -> fn_case.condition end)

          opposite_condition =
            Tla.Generator.Models.Function.Condition.get_opposite_condition(previous_conditions)

          new_case = %Tla.Generator.Models.Function.Case{
            condition: opposite_condition,
            return: fn_case.return
          }

          acc ++ [new_case]
        end
      end)

    ordered_cases
  end
end
