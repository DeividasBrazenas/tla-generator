defmodule Generated.HandleProposeMessage do
  def handle_message(rbc, {:PROPOSE, from, value} = _msg) do

    broadcaster = rbc.broadcaster
    echo_sent = rbc.echo_sent
    me = rbc.me
    msg_recv = rbc.msg_recv
    output = rbc.output
    peers = rbc.peers
    predicate = rbc.predicate

    ^broadcaster = from

    if (not echo_sent and predicate.(value)) do
      msg_recv = Map.put(msg_recv, {from, :PROPOSE}, true)

      rbc = %{rbc | echo_sent: true, msg_recv: msg_recv}

      msgs = Enum.into(peers, %{}, fn peer_id -> {peer_id, [{:ECHO, me, value}]} end)

      {:ok, rbc, msgs, output}

    else
      msgs = %{}

      {:ok, rbc, msgs, output}

    end
  end
end
