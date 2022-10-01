defmodule Tla.Generator.Models.Function.Body.Action do
  use TypedStruct

  typedstruct do
    @typedoc "Type for a function body action"
  end

  @callback get(any()) :: any()
end
