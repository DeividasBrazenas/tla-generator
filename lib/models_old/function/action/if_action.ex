defmodule Tla.Generator.Models.Function.Body.Action.If do
  @behaviour Tla.Generator.Models.Function.Body.Action

  use TypedStruct

  typedstruct do
    @typedoc "Type for if action"
    field(:condition, Tla.Generator.Models.Function.Condition.t(), default: nil)
    field(:actions, List[Tla.Generator.Models.Function.Body.Action.t()], default: [])
  end

  @impl Tla.Generator.Models.Function.Body.Action
  def get(_any) do
    action = %Tla.Generator.Models.Function.Body.Action.If{
      condition: Tla.Generator.Models.Function.Condition.get("") # TODO
    }

    action
  end
end
