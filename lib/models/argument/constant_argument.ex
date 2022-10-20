defmodule Models.Argument.Constant do
  @moduledoc """
  Defines a constant argument
  """
  @behaviour Models.Argument

  use TypedStruct

  typedstruct do
    field(:value, any(), default: nil, enforce: true)
  end

  @impl Models.Argument
  @spec parse_argument(any(), any()) :: Models.Argument.Constant.t()
  def parse_argument(constant, _) do
    argument = %Models.Argument.Constant{
      value: constant
    }

    argument
  end
end
