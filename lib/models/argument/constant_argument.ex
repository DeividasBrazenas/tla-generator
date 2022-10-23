defmodule Models.Argument.Constant do
  @moduledoc """
  Defines a constant argument
  """
  @behaviour Models.Argument

  use TypedStruct

  typedstruct do
    field(:value, any(), default: nil, enforce: true)
    field(:name, atom(), default: nil)
  end

  @impl Models.Argument
  @spec parse_argument(any(), any()) :: Models.Argument.Constant.t()
  def parse_argument(constant, %{name: name}) do
    argument = %Models.Argument.Constant{
      value: constant,
      name: name
    }

    argument
  end

  @impl Models.Argument
  @spec has_constant(Models.Argument.Constant.t()) :: boolean()
  def has_constant(_) do
    true
  end
end
