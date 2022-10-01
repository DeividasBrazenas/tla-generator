defmodule Tla.Generator.Models.Function.Body.Action.Return do
  @behaviour Tla.Generator.Models.Function.Body.Action

  use TypedStruct

  typedstruct do
    @typedoc "Type for return action"
    field(:value, atom(), default: nil)
  end

  @impl Tla.Generator.Models.Function.Body.Action
  def get(_any) do
    action = %Tla.Generator.Models.Function.Body.Action.Return{
      value: "" # TODO
    }
    action
  end
end
