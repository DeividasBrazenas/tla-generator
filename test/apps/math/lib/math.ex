defmodule Math do
  use Extractors.PlusCal

  use TypedStruct

  typedstruct do
    field(:operator, atom(), default: nil, enforce: true)
    field(:left_operand, atom(), default: nil, enforce: true)
    field(:right_operand, atom(), default: nil, enforce: true)
  end

  @tla_generation_defs :min
  @spec min(integer(), integer()) :: integer()
  def min(a, b) when a > b, do: b
  def min(a, _), do: a

  @tla_generation_defs :max
  @spec max(integer(), integer()) :: integer()
  def max(a, b) when a < b, do: b
  def max(a, _), do: a

  @tla_generation_defs :compare
  @spec compare({atom(), any(), any()}) :: any()
  def compare({:<, a, b}), do: a
  def compare({_, "a", b}), do: b
  def compare({_, a, 7}), do: a

  @tla_generation_defs :compare_v2
  @spec compare_v2(atom(), any(), any()) :: any()
  def compare_v2(:<, a, b), do: a
  def compare_v2(:>, "a", b), do: b
  def compare_v2(_, a, {b, 7}), do: a
  def compare_v2(x = %Math{operator: :<}, a, {b, 7}), do: a
  def compare_v2(%Math{operator: %{a: :b}}, a, {b, 7}), do: a
end
