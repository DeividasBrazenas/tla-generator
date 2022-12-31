defmodule Config.Variable do
  use TypedStruct

  @derive [Poison.Encoder]
  typedstruct do
    field(:name, String.t())
    field(:assignment_lines, List[String.t()])
  end
end
