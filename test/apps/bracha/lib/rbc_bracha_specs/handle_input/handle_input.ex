defmodule Generated.HandleInput do
  def handle_input(rbc, input) do
    broadcaster = rbc.broadcaster
    me = rbc.me
    output = rbc.output
    peers = rbc.peers
    propose_sent = rbc.propose_sent

    ^broadcaster = me

    ^propose_sent = false

    rbc = %{rbc | propose_sent: true}

    msgs = Enum.into(peers, %{}, fn peer_id -> {peer_id, [{:PROPOSE, me, input}]} end)

    {:ok, rbc, msgs, output}
  end
end