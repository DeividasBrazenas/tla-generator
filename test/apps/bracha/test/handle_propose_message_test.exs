defmodule HandleProposeTest do
  use ExUnit.Case

  test "from is not broadcaster throws exception (original)",
    do: test_from_is_not_broadcaster(&Wasper.HBBFT.RBC.Bracha.handle_message/2)

  test "me is not broadcaster throws exception (generated)",
    do: test_from_is_not_broadcaster(&Generated.HandleProposeMessage.handle_message/2)

  defp test_from_is_not_broadcaster(handle_message) do
    assert_raise MatchError, "no match of right hand side value: :n_3", fn ->
      msg = {:PROPOSE, :n_3, "value"}

      handle_message.(
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
        msg
      )
    end
  end

  test "echo already sent returns correct result (original)",
    do: test_echo_already_sent(&Wasper.HBBFT.RBC.Bracha.handle_message/2)

  test "echo already sent returns correct result (generated)",
    do: test_echo_already_sent(&Generated.HandleProposeMessage.handle_message/2)

  defp test_echo_already_sent(handle_message) do
    msg = {:PROPOSE, :n_2, "value"}

    {:ok, rbc, msgs, output} =
      handle_message.(
        %Wasper.HBBFT.RBC.Bracha{
          me: :n_1,
          broadcaster: :n_2,
          peers: [:n_1, :n_2, :n_3],
          n: 3,
          f: 1,
          echo_sent: true,
          predicate: fn _ -> true end,
          max_msg_size: 1000,
          output: nil
        },
        msg
      )

    assert msgs == %{}
    assert output == nil
  end

  test "false predicate returns correct result (original)",
    do: test_false_predicate(&Wasper.HBBFT.RBC.Bracha.handle_message/2)

  test "false predicate returns correct result (generated)",
    do: test_false_predicate(&Generated.HandleProposeMessage.handle_message/2)

  defp test_false_predicate(handle_message) do
    msg = {:PROPOSE, :n_2, "value"}

    {:ok, rbc, msgs, output} =
      handle_message.(
        %Wasper.HBBFT.RBC.Bracha{
          me: :n_1,
          broadcaster: :n_2,
          peers: [:n_1, :n_2, :n_3],
          n: 3,
          f: 1,
          echo_sent: false,
          predicate: fn _ -> false end,
          max_msg_size: 1000,
          output: nil
        },
        msg
      )

    assert msgs == %{}
    assert output == nil
  end

  test "echo message is sent (original)",
    do: test_echo_message_is_sent(&Wasper.HBBFT.RBC.Bracha.handle_message/2)

  test "echo message is sent (generated)",
    do: test_echo_message_is_sent(&Generated.HandleProposeMessage.handle_message/2)

  defp test_echo_message_is_sent(handle_message) do
    msg = {:PROPOSE, :n_2, "value"}
    me = :n_1
    peers = [:n_1, :n_2, :n_3]

    {:ok, rbc, msgs, output} =
      handle_message.(
        %Wasper.HBBFT.RBC.Bracha{
          me: me,
          broadcaster: :n_2,
          peers: peers,
          n: 3,
          f: 1,
          echo_sent: false,
          predicate: fn _ -> true end,
          max_msg_size: 1000,
          output: nil
        },
        msg
      )

    assert rbc.echo_sent == true
    assert Map.get(rbc.msg_recv, {:n_2, :PROPOSE}) == true

    Enum.each(peers, fn peer ->
      peer_msgs = Map.get(msgs, peer)

      assert Enum.any?(peer_msgs, fn {type, from, value} ->
               type == :ECHO and from == me and value == "value"
             end)
    end)

    assert output == nil
  end
end
