defmodule HandleInputTest do
  use ExUnit.Case

  test "me is not broadcaster throws exception (original)",
    do: test_me_is_not_broadcaster(&Wasper.HBBFT.RBC.Bracha.handle_input/2)

  test "me is not broadcaster throws exception (generated)",
    do: test_me_is_not_broadcaster(&Generated.HandleInput.handle_input/2)

  defp test_me_is_not_broadcaster(handle_input) do
    assert_raise MatchError, "no match of right hand side value: :n_1", fn ->
      handle_input.(
        %Wasper.HBBFT.RBC.Bracha{
          me: :n_1,
          broadcaster: :n_2,
          peers: [:n_1, :n_2, :n_3],
          n: 3,
          f: 1,
          propose_sent: false,
          predicate: fn _ -> true end,
          max_msg_size: 1000,
          output: nil
        },
        "value"
      )
    end
  end

  test "propose already sent throws exception (original)",
    do: test_propose_already_sent(&Wasper.HBBFT.RBC.Bracha.handle_input/2)

  test "propose already sent throws exception (generated)",
    do: test_propose_already_sent(&Generated.HandleInput.handle_input/2)

  defp test_propose_already_sent(handle_input) do
    assert_raise MatchError, "no match of right hand side value: false", fn ->
      handle_input.(
        %Wasper.HBBFT.RBC.Bracha{
          me: :n_1,
          broadcaster: :n_1,
          peers: [:n_1, :n_2, :n_3],
          n: 3,
          f: 1,
          propose_sent: true,
          predicate: fn _ -> true end,
          max_msg_size: 1000,
          output: nil
        },
        "value"
      )
    end
  end

  test "propose message is sent (original)",
    do: test_propose_message_is_sent(&Wasper.HBBFT.RBC.Bracha.handle_input/2)

  test "propose message is sent (generated)",
    do: test_propose_message_is_sent(&Generated.HandleInput.handle_input/2)

  defp test_propose_message_is_sent(handle_input) do
    broadcaster = :n_1
    peers = [:n_1, :n_2, :n_3]
    broadcast_value = "value"

    {:ok, rbc, msgs, output} =
      handle_input.(
        %Wasper.HBBFT.RBC.Bracha{
          me: broadcaster,
          broadcaster: broadcaster,
          peers: peers,
          n: 3,
          f: 1,
          propose_sent: false,
          predicate: fn _ -> true end,
          max_msg_size: 1000,
          output: nil
        },
        broadcast_value
      )

    assert rbc.propose_sent == true

    Enum.each(peers, fn peer ->
      peer_msgs = Map.get(msgs, peer)

      assert Enum.any?(peer_msgs, fn {type, from, value} ->
               type == :PROPOSE and from == broadcaster and value == broadcast_value
             end)
    end)

    assert output == nil
  end
end
