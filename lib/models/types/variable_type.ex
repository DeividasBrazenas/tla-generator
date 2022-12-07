defmodule Models.Type.Variable do
  @moduledoc """
  Defines a constant argument
  """
  @behaviour Models.Type

  use TypedStruct

  typedstruct do
    field(:name, atom(), default: nil, enforce: true)
  end

  @impl Models.Type
  @spec parse_type(any(), any()) :: Models.Type.Variable.t()
  def parse_type(name, _) do
    argument = %Models.Type.Variable{
      name: name
    }

    argument
  end

  @impl Models.Type
  @spec has_constant(Models.Type.Variable.t()) :: boolean()
  def has_constant(_) do
    false
  end
end
