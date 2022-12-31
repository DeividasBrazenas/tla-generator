### Copyright 2022 Karolis Petrauskas
### SPDX-License-Identifier: Apache-2.0
defmodule Wasper.HBBFT.RBC.Bracha do
  @moduledoc """
  This module implements the Bracha's Reliable Broadcast.
  The original version of this RBC can be found here (see "FIG. 1. The broadcast primitive"):

    Gabriel Bracha. 1987. Asynchronous byzantine agreement protocols. Inf. Comput.
    75, 2 (November 1, 1987), 130–143. DOI:https://doi.org/10.1016/0890-5401(87)90054-X

  Here we follow the algorithm presentation from (see "Algorithm 2 Bracha’s RBC [14]"):

    Sourav Das, Zhuolun Xiang, and Ling Ren. 2021. Asynchronous Data Dissemination
    and its Applications. In Proceedings of the 2021 ACM SIGSAC Conference on Computer
    and Communications Security (CCS '21). Association for Computing Machinery,
    New York, NY, USA, 2705–2721. DOI:https://doi.org/10.1145/3460120.3484808

  The algorithms differs a bit. The latter supports predicates and also it don't
  imply sending ECHO messages upon receiving F+1 READY messages. The pseudo-code
  from the Das et al.:

    01: // only broadcaster node
    02: input 𝑀
    03: send ⟨PROPOSE, 𝑀⟩ to all
    04: // all nodes
    05: input 𝑃(·) // predicate 𝑃(·) returns true unless otherwise specified.
    06: upon receiving ⟨PROPOSE, 𝑀⟩ from the broadcaster do
    07:     if 𝑃(𝑀) then
    08:         send ⟨ECHO, 𝑀⟩ to all
    09: upon receiving 2𝑡 + 1 ⟨ECHO, 𝑀⟩ messages and not having sent a READY message do
    10:     send ⟨READY, 𝑀⟩ to all
    11: upon receiving 𝑡 + 1 ⟨READY, 𝑀⟩ messages and not having sent a READY message do
    12:     send ⟨READY, 𝑀⟩ to all
    13: upon receiving 2𝑡 + 1 ⟨READY, 𝑀⟩ messages do
    14:     output 𝑀

  In the above 𝑡 is "Given a network of 𝑛 nodes, of which up to 𝑡 could be malicious",
  thus that's the parameter F in the specification bellow.

  On the predicates. If they are updated via `MakePredicateUpdateMsg` and similar,
  they have to be monotonic. I.e. if a predicate was true for the broadcaster's
  message, then all the following predicates supplied to the algorithm must be
  true for that message as well.

  Similar implementation in golang along with the TLA+ specification can be found here:
  <https://github.com/iotaledger/wasp/blob/develop/packages/gpa/rbc/bracha/bracha.go>
  """

  alias Wasper.HBBFT.RBC.Bracha, as: RBC
  alias Wasper.GenPureAlg, as: GPA

  use Extractors.PlusCal

  @behaviour GPA

  @type peer_id() :: any()
  @type msg_type() :: :PROPOSE | :ECHO | :READY
  @type msg() :: {type :: msg_type(), from :: peer_id(), value :: binary()}

  @type t() :: %RBC{
          n: integer(),
          f: integer(),
          me: peer_id(),
          peers: [peer_id()],
          broadcaster: peer_id(),
          predicate: (binary() -> boolean()),
          max_msg_size: integer(),
          propose_sent: boolean(),
          msg_recv: %{{peer_id(), msg_type()} => boolean()},
          echo_sent: boolean(),
          echo_recv: %{(hash :: binary()) => %{peer_id() => boolean()}},
          ready_sent: boolean(),
          ready_recv: %{(hash :: binary()) => %{peer_id() => boolean()}},
          output: binary() | nil
        }
  @enforce_keys [:n, :f, :me, :peers, :broadcaster, :predicate, :max_msg_size]
  defstruct n: nil,
            f: nil,
            me: nil,
            peers: nil,
            broadcaster: nil,
            max_msg_size: nil,
            predicate: nil,
            propose_sent: false,
            msg_recv: %{},
            echo_sent: false,
            echo_recv: %{},
            ready_sent: false,
            ready_recv: %{},
            output: nil

  ### ==========================================================================
  ### API
  ### ==========================================================================

  @spec new(
          f :: integer(),
          me :: peer_id(),
          peers :: [peer_id()],
          broadcaster :: peer_id(),
          predicate :: (binary() -> bool),
          max_msg_size :: integer()
        ) :: GPA.t(t())
  def new(f, me, peers, broadcaster, predicate, max_msg_size) do
    {:ok, ref, msgs, nil} = GPA.new(RBC, me, {f, me, peers, broadcaster, predicate, max_msg_size})
    0 = map_size(msgs)
    ref
  end

  @spec input(GPA.t(t()), binary()) :: GPA.ret(GPA.t(t()))
  def input(ref, input), do: GPA.input(ref, input)

  @spec message(GPA.t(t()), msg()) :: GPA.ret(GPA.t(t()))
  def message(ref, message), do: GPA.message(ref, message)

  ### ==========================================================================
  ### Callbacks for GPA
  ### ==========================================================================

  @impl GPA
  @spec handle_new(
          {f :: integer(), me :: peer_id(), peers :: [peer_id()], broadcaster :: peer_id(),
           predicate :: (binary() -> bool), max_msg_size :: integer()}
        ) :: GPA.ret(t())
  def handle_new({f, me, peers, broadcaster, predicate, max_msg_size}) do
    n = length(peers)
    true = n >= 3 * f + 1

    rbc = %RBC{
      n: n,
      f: f,
      me: me,
      peers: peers,
      broadcaster: broadcaster,
      predicate: predicate,
      max_msg_size: max_msg_size
    }

    {:ok, rbc, %{}, nil}
  end

  @impl GPA
  @spec handle_input(t(), binary()) :: GPA.ret(t())
  # 01: // only broadcaster node
  # 02: input 𝑀
  # 03: send ⟨PROPOSE, 𝑀⟩ to all
  @tlagen_function :handle_input
  def handle_input(rbc, input) do
    %RBC{
      me: me,
      broadcaster: broadcaster,
      peers: peers,
      propose_sent: propose_sent,
      output: output
    } = rbc

    ^broadcaster = me
    ^propose_sent = false
    rbc = %RBC{rbc | propose_sent: true}

    msgs = Enum.into(peers, %{}, fn peer_id -> {peer_id, [{:PROPOSE, me, input}]} end)

    {:ok, rbc, msgs, output}
  end

  @impl GPA
  @spec handle_message(t(), msg()) :: GPA.ret(t())
  # 06: upon receiving ⟨PROPOSE, 𝑀⟩ from the broadcaster do
  # 07:     if 𝑃(𝑀) then
  # 08:         send ⟨ECHO, 𝑀⟩ to all
  @tlagen_function :handle_propose_message
  def handle_message(rbc, {:PROPOSE, from, value} = _msg) do
    %RBC{
      me: me,
      broadcaster: broadcaster,
      peers: peers,
      predicate: predicate,
      output: output,
      echo_sent: echo_sent,
      msg_recv: msg_recv
    } = rbc

    ^broadcaster = from

    if not echo_sent and predicate.(value) do
      msg_recv = Map.put(msg_recv, {from, :PROPOSE}, true)
      rbc = %RBC{rbc | echo_sent: true, msg_recv: msg_recv}

      msgs = Enum.into(peers, %{}, fn peer_id -> {peer_id, [{:ECHO, me, value}]} end)

      {:ok, rbc, msgs, output}
    else
      msgs = %{}
      {:ok, rbc, msgs, output}
    end
  end

  # 09: upon receiving 2𝑡 + 1 ⟨ECHO, 𝑀⟩ messages and not having sent a READY message do
  # 10:     send ⟨READY, 𝑀⟩ to all
  @tlagen_function :handle_echo_message
  def handle_message(rbc, {:ECHO, from, value} = _msg) do
    %RBC{me: me, n: n, f: f, peers: peers, msg_recv: msg_recv,
         echo_recv: echo_recv, ready_sent: ready_sent, output: output} = rbc

    existing_recv = Map.get(echo_recv, value, %{})
    value_recv = Map.put(existing_recv, from, true)
    echo_recv = Map.put(echo_recv, value, value_recv)

    rbc = %RBC{rbc | echo_recv: echo_recv}

    count = map_size(value_recv)

    if not ready_sent and count > (n + f) / 2 do
      msg_recv = Map.put(msg_recv, {from, :ECHO}, true)
      rbc = %RBC{rbc | ready_sent: true, msg_recv: msg_recv}

      msgs = Enum.into(peers, %{}, fn peer_id -> {peer_id, [{:READY, me, value}]} end)
      {:ok, rbc, msgs, output}
    else
      msgs = %{}
      {:ok, rbc, msgs, output}
    end
  end

  # 11: upon receiving 𝑡 + 1 ⟨READY, 𝑀⟩ messages and not having sent a READY message do
  # 12:     send ⟨READY, 𝑀⟩ to all
  # 13: upon receiving 2𝑡 + 1 ⟨READY, 𝑀⟩ messages do
  # 14:     output 𝑀
  @tlagen_function :handle_ready_message
  def handle_message(rbc, {:READY, from, value} = _msg) do
    %RBC{
      me: me,
      f: f,
      peers: peers,
      msg_recv: msg_recv,
      ready_recv: ready_recv,
      ready_sent: ready_sent,
      output: output
    } = rbc

    existing_recv = Map.get(ready_recv, value, %{})
    value_recv = Map.put(existing_recv, from, true)
    ready_recv = Map.put(ready_recv, value, value_recv)

    rbc = %RBC{rbc | ready_recv: ready_recv}

    count = map_size(value_recv)

    output =
      cond do
        count > 3 * f and output == nil -> value
        true -> output
      end

    if not ready_sent and count > f do
      msg_recv = Map.put(msg_recv, {from, :READY}, true)
      rbc = %RBC{rbc | ready_sent: true, msg_recv: msg_recv}

      msgs = Enum.into(peers, %{}, fn peer_id -> {peer_id, [{:READY, me, value}]} end)

      {:ok, rbc, msgs, output}
    else
      msgs = %{}
      {:ok, rbc, msgs, output}
    end
  end
end
