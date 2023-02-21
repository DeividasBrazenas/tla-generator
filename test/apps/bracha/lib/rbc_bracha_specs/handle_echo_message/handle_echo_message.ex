defmodule Generated.HandleEchoMessage do
  def handle_message(rbc, {:ECHO, from, value} = _msg) do

    echo_recv = rbc.echo_recv
    f = rbc.f
    me = rbc.me
    msg_recv = rbc.msg_recv
    n = rbc.n
    output = rbc.output
    peers = rbc.peers
    ready_sent = rbc.ready_sent

    existing_recv = Map.get(echo_recv, value, %{})

    value_recv = Map.put(existing_recv, from, true)

    echo_recv = Map.put(echo_recv, value, value_recv)

    rbc = %{rbc | echo_recv: echo_recv}

    count = map_size(value_recv)

    if (not ready_sent and (count > ((n + f) / 2))) do
      msg_recv = Map.put(msg_recv, {from, :ECHO}, true)

      rbc = %{rbc | msg_recv: msg_recv, ready_sent: true}

      msgs = Enum.into(peers, %{}, fn peer_id -> {peer_id, [{:READY, me, value}]} end)

      {:ok, rbc, msgs, output}

    else
      msgs = %{}

      {:ok, rbc, msgs, output}

    end
  end
end
