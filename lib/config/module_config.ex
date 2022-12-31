defmodule Config.Module do
  use TypedStruct

  @derive [Poison.Encoder]
  typedstruct do
    field(:module_name, String.t())
    field(:functions, List[Config.Function.t()], default: [])
  end

  @spec get_config(String.t()) :: Config.Module.t()
  def get_config(file_path) do
    with {:ok, body} <- File.read(file_path),
         {:ok, json} <-
           Poison.decode(body, %{
             as: %Config.Module{
               functions: [
                 %Config.Function{
                   global_variables: [%Config.Variable{}],
                   local_variables: [%Config.Variable{}]
                 }
               ]
             }
           }),
         do: json
  end
end
