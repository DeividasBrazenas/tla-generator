defmodule Models.Type.Constant do
  @moduledoc """
  Defines a constant argument
  """
  @behaviour Models.Type

  use TypedStruct

  typedstruct do
    field(:value, any(), default: nil, enforce: true)
    field(:name, atom(), default: nil)
  end

  @impl Models.Type
  @spec parse_type(any(), any()) :: Models.Type.Constant.t()
  def parse_type(constant, %{name: name}) do
    argument = %Models.Type.Constant{
      value: constant,
      name: name
    }

    argument
  end

  @impl Models.Type
  @spec has_constant(Models.Type.Constant.t()) :: boolean()
  def has_constant(_) do
    true
  end
end
