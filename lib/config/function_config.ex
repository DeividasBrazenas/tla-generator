defmodule Config.Function do
  use TypedStruct

  @derive [Poison.Encoder]
  typedstruct do
    field(:function_name, String.t())
    field(:process, String.t())
    field(:extensions, List[String.t()], default: [])
    field(:constants, List[String.t()], default: [])
    field(:global_variables, List[Config.Variable.t()], default: [])
    field(:local_variables, List[Config.Variable.t()], default: [])
    field(:definitions, List[String.t()], default: [])
  end
end
