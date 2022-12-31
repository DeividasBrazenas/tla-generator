### Copyright 2022 Karolis Petrauskas
### SPDX-License-Identifier: Apache-2.0
defmodule Wasper.HBBFT.RBC.Bracha.Test do
  alias Wasper.HBBFT.RBC.Bracha, as: RBC
  alias Wasper.GenPureAlg, as: GPA
  use ExUnit.Case

  test "n=1", do: test_randomized(1, 0, "something important")
  test "n=2", do: test_randomized(2, 0, "something important")
  test "n=3", do: test_randomized(3, 0, "something important")
  test "n=4", do: test_randomized(4, 1, "something important")
  test "n=31", do: test_randomized(31, 10, "something important")
  test "n=100 (Δt=1.3s)", do: test_randomized(100, 33, "something important")

  defp test_randomized(n, f, input) do
    broadcaster = 1
    peer_ids = Enum.to_list(1..n)

    rbcs =
      for peer_id <- peer_ids, into: %{} do
        {peer_id, RBC.new(f, peer_id, peer_ids, broadcaster, fn _value -> true end, 1_000_000)}
      end

    inps = %{broadcaster => input}
    {:ok, rbcs, outs} = GPA.combined_input(rbcs, inps)

    Enum.each(peer_ids, fn peer_id ->
      assert outs[peer_id] == input
    end)
  end
end
