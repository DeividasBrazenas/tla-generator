defmodule Math do
  use Extractors.PlusCal

  use TypedStruct

  typedstruct do
    field(:operator, atom(), default: nil, enforce: true)
    field(:left_operand, atom(), default: nil, enforce: true)
    field(:right_operand, atom(), default: nil, enforce: true)
  end

  # @pluscal_process :min
  # @spec min(integer(), integer()) :: integer()
  # def min(a, b) when a > b, do: b
  # def min(a, _), do: a

  # @pluscal_process :max
  # @spec max(integer(), integer()) :: integer()
  # def max(a, b) when a < b, do: b
  # def max(a, _), do: a

  # @pluscal_process :compare
  # @spec compare({atom(), any(), any()}) :: any()
  # def compare({:<, a, b}), do: a
  # def compare({_, "a", b}), do: b
  # def compare({_, a, 7}), do: a

  @pluscal_process :compare_v2
  @spec compare_v2(atom(), any(), any()) :: any()
  def compare_v2(x = %Math{operator: :<}, a, {b, 7}) when a > b, do: a
  # def compare_v2(%{a: :b}, a, {b, 7}), do: a
  # def compare_v2(:>, "a", {b, "c"}), do: b
  # def compare_v2(_, a, {b, 7}), do: a
  # def compare_v2(%Math{operator: %{a: :b}}, a, {b, 7}), do: a
  # def compare_v2(map = %{operator: z}, {b, 7}, named_tuple = {b, 7}), do: z
end
