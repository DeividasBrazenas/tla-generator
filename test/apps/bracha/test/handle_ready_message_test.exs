defmodule HandleReadyTest do
  use ExUnit.Case

  test "ready message not sent (original)",
    do: test_ready_message_not_sent(&Wasper.HBBFT.RBC.Bracha.handle_message/2)

  test "ready message not sent (generated)",
    do: test_ready_message_not_sent(&Generated.HandleReadyMessage.handle_message/2)

  defp test_ready_message_not_sent(handle_message) do
    msg = {:READY, :n_2, "value"}
    me = :n_1
    peers = [:n_1, :n_2, :n_3, :n_4]

    {:ok, rbc, msgs, output} =
      handle_message.(
        %Wasper.HBBFT.RBC.Bracha{
          me: :n_1,
          broadcaster: :n_3,
          peers: peers,
          n: 4,
          f: 1,
          ready_sent: false,
          predicate: fn _ -> true end,
          max_msg_size: 1000,
          output: nil
        },
        msg
      )

    assert rbc.ready_recv == %{"value" => %{n_2: true}}
    assert msgs == %{}
    assert output == nil
  end

  test "ready already sent returns correct result (original)",
    do: test_ready_already_sent(&Wasper.HBBFT.RBC.Bracha.handle_message/2)

  test "ready already sent returns correct result (generated)",
    do: test_ready_already_sent(&Generated.HandleReadyMessage.handle_message/2)

  defp test_ready_already_sent(handle_message) do
    msg = {:READY, :n_2, "value"}
    ready_recv = %{"value" => %{n_1: true}}

    {:ok, rbc, msgs, output} =
      handle_message.(
        %Wasper.HBBFT.RBC.Bracha{
          me: :n_1,
          broadcaster: :n_3,
          peers: [:n_1, :n_2, :n_3, :n_4],
          n: 4,
          f: 1,
          ready_recv: ready_recv,
          ready_sent: true,
          predicate: fn _ -> true end,
          max_msg_size: 1000,
          output: nil
        },
        msg
      )

    assert rbc.ready_recv == %{"value" => %{n_1: true, n_2: true}}
    assert msgs == %{}
    assert output == nil
  end

  test "ready message is sent but output is not set (original)",
    do:
      test_ready_message_is_sent_but_output_is_not_set(&Wasper.HBBFT.RBC.Bracha.handle_message/2)

  test "ready message is sent but output is not set (generated)",
    do:
      test_ready_message_is_sent_but_output_is_not_set(
        &Generated.HandleReadyMessage.handle_message/2
      )

  defp test_ready_message_is_sent_but_output_is_not_set(handle_message) do
    msg = {:READY, :n_2, "value"}
    me = :n_1
    peers = [:n_1, :n_2, :n_3, :n_4]
    ready_recv = %{"value" => %{n_1: true}}

    {:ok, rbc, msgs, output} =
      handle_message.(
        %Wasper.HBBFT.RBC.Bracha{
          me: :n_1,
          broadcaster: :n_3,
          peers: peers,
          n: 4,
          f: 1,
          ready_recv: ready_recv,
          ready_sent: false,
          predicate: fn _ -> true end,
          max_msg_size: 1000,
          output: nil
        },
        msg
      )

    assert rbc.ready_recv == %{"value" => %{n_1: true, n_2: true}}

    Enum.each(peers, fn peer ->
      peer_msgs = Map.get(msgs, peer)

      assert Enum.any?(peer_msgs, fn {type, from, value} ->
               type == :READY and from == me and value == "value"
             end)
    end)

    assert output == nil
  end

  test "output is not set when not nil (original)",
    do: test_output_is_not_set_when_not_nil(&Wasper.HBBFT.RBC.Bracha.handle_message/2)

  test "output is not set when not nil (generated)",
    do: test_output_is_not_set_when_not_nil(&Generated.HandleReadyMessage.handle_message/2)

  defp test_output_is_not_set_when_not_nil(handle_message) do
    msg = {:READY, :n_2, "value"}
    me = :n_1
    peers = [:n_1, :n_2, :n_3, :n_4]
    ready_recv = %{"value" => %{n_1: true, n_3: true, n_4: true}}

    {:ok, rbc, msgs, output} =
      handle_message.(
        %Wasper.HBBFT.RBC.Bracha{
          me: :n_1,
          broadcaster: :n_3,
          peers: peers,
          n: 4,
          f: 1,
          ready_recv: ready_recv,
          ready_sent: true,
          predicate: fn _ -> true end,
          max_msg_size: 1000,
          output: "not nil"
        },
        msg
      )

    assert rbc.ready_recv == %{"value" => %{n_1: true, n_2: true, n_3: true, n_4: true}}
    assert msgs == %{}
    assert output == "not nil"
  end

  test "output is set (original)",
    do: test_output_is_set(&Wasper.HBBFT.RBC.Bracha.handle_message/2)

  test "output is set (generated)",
    do: test_output_is_set(&Generated.HandleReadyMessage.handle_message/2)

  defp test_output_is_set(handle_message) do
    msg = {:READY, :n_2, "value"}
    me = :n_1
    peers = [:n_1, :n_2, :n_3, :n_4]
    ready_recv = %{"value" => %{n_1: true, n_3: true, n_4: true}}

    {:ok, rbc, msgs, output} =
      handle_message.(
        %Wasper.HBBFT.RBC.Bracha{
          me: :n_1,
          broadcaster: :n_3,
          peers: peers,
          n: 4,
          f: 1,
          ready_recv: ready_recv,
          ready_sent: true,
          predicate: fn _ -> true end,
          max_msg_size: 1000,
          output: nil
        },
        msg
      )

    assert rbc.ready_recv == %{"value" => %{n_1: true, n_2: true, n_3: true, n_4: true}}
    assert msgs == %{}
    assert output == "value"
  end
end
