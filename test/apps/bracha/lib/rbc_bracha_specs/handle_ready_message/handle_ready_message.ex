defmodule Generated.HandleReadyMessage do
  def handle_message(rbc, {:READY, from, value} = _msg) do

    f = rbc.f
    me = rbc.me
    msg_recv = rbc.msg_recv
    output = rbc.output
    peers = rbc.peers
    ready_recv = rbc.ready_recv
    ready_sent = rbc.ready_sent

    existing_recv = Map.get(ready_recv, value, %{})

    value_recv = Map.put(existing_recv, from, true)

    ready_recv = Map.put(ready_recv, value, value_recv)

    rbc = %{rbc | ready_recv: ready_recv}

    count = map_size(value_recv)

    output =
      cond do
        ((count > (3 * f)) and (output == nil)) -> value
        true -> output
      end

    if (not ready_sent and (count > f)) do
      msg_recv = Map.put(msg_recv, {from, :READY}, true)

      rbc = %{rbc | msg_recv: msg_recv, ready_sent: true}

      msgs = Enum.into(peers, %{}, fn peer_id -> {peer_id, [{:READY, me, value}]} end)

      {:ok, rbc, msgs, output}

    else
      msgs = %{}

      {:ok, rbc, msgs, output}

    end
  end
end