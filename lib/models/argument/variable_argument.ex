defmodule Models.Argument.Variable do
  @moduledoc """
  Defines a constant argument
  """
  @behaviour Models.Argument

  use TypedStruct

  typedstruct do
    field(:name, atom(), default: nil, enforce: true)
  end

  @impl Models.Argument
  @spec parse_argument(any(), any()) :: Models.Argument.Variable.t()
  def parse_argument(name, _) do
    argument = %Models.Argument.Variable{
      name: name
    }

    argument
  end
end
