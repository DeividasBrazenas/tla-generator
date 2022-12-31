defmodule Expression do
  use TypedStruct

  typedstruct do
    field(:name, atom())
    field(:lines, List[String.t()], default: [])
    field(:variables, List[String.t()], default: [])
    field(:definitions, List[String.t()], default: [])
    field(:labels_count, Integer.t(), default: 0)
  end
end
