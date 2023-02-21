defmodule HandleEchoTest do
  use ExUnit.Case

  test "ready already sent returns correct result (original)",
    do: test_ready_already_sent(&Wasper.HBBFT.RBC.Bracha.handle_message/2)

  test "ready already sent returns correct result (generated)",
    do: test_ready_already_sent(&Generated.HandleEchoMessage.handle_message/2)

  defp test_ready_already_sent(handle_message) do
    msg = {:ECHO, :n_2, "value"}
    echo_recv = %{"value" => %{n_1: true, n_3: true, n_4: true}}

    {:ok, rbc, msgs, output} =
      handle_message.(
        %Wasper.HBBFT.RBC.Bracha{
          me: :n_1,
          broadcaster: :n_3,
          peers: [:n_1, :n_2, :n_3, :n_4],
          n: 4,
          f: 1,
          echo_recv: echo_recv,
          ready_sent: true,
          predicate: fn _ -> true end,
          max_msg_size: 1000,
          output: nil
        },
        msg
      )

    assert rbc.echo_recv == %{"value" => %{n_1: true, n_2: true, n_3: true, n_4: true}}
    assert msgs == %{}
    assert output == nil
  end

  test "not enough echo messages returns correct result (original)",
    do: test_not_enough_echo_messages(&Wasper.HBBFT.RBC.Bracha.handle_message/2)

  test "not enough echo messages returns correct result (generated)",
    do: test_not_enough_echo_messages(&Generated.HandleEchoMessage.handle_message/2)

  defp test_not_enough_echo_messages(handle_message) do
    msg = {:ECHO, :n_2, "value"}
    echo_recv = %{"value" => %{n_3: true}}

    {:ok, rbc, msgs, output} =
      handle_message.(
        %Wasper.HBBFT.RBC.Bracha{
          me: :n_1,
          broadcaster: :n_3,
          peers: [:n_1, :n_2, :n_3, :n_4],
          n: 4,
          f: 1,
          ready_sent: false,
          echo_recv: echo_recv,
          predicate: fn _ -> true end,
          max_msg_size: 1000,
          output: nil
        },
        msg
      )

    assert rbc.echo_recv == %{"value" => %{n_2: true, n_3: true}}
    assert msgs == %{}
    assert output == nil
  end

  test "ready message is sent (original)",
    do: test_ready_message_is_sent(&Wasper.HBBFT.RBC.Bracha.handle_message/2)

  test "ready message is sent (generated)",
    do: test_ready_message_is_sent(&Generated.HandleEchoMessage.handle_message/2)

  defp test_ready_message_is_sent(handle_message) do
    msg = {:ECHO, :n_2, "value"}
    me = :n_1
    echo_recv = %{"value" => %{n_3: true, n_4: true}}
    peers = [:n_1, :n_2, :n_3, :n_4]

    {:ok, rbc, msgs, output} =
      handle_message.(
        %Wasper.HBBFT.RBC.Bracha{
          me: me,
          broadcaster: :n_3,
          peers: peers,
          n: 4,
          f: 1,
          ready_sent: false,
          echo_recv: echo_recv,
          predicate: fn _ -> true end,
          max_msg_size: 1000,
          output: nil
        },
        msg
      )

    assert rbc.echo_recv == %{"value" => %{n_2: true, n_3: true, n_4: true}}
    assert rbc.ready_sent == true
    assert Map.get(rbc.msg_recv, {:n_2, :ECHO}) == true

    Enum.each(peers, fn peer ->
      peer_msgs = Map.get(msgs, peer)

      assert Enum.any?(peer_msgs, fn {type, from, value} ->
               type == :READY and from == me and value == "value"
             end)
    end)

    assert output == nil
  end
end
