### Copyright 2022 Karolis Petrauskas
### SPDX-License-Identifier: Apache-2.0
defmodule Wasper.GenPureAlg do
  alias Wasper.GenPureAlg, as: GPA

  @moduledoc """
  Generic algorithm implemented as a side-effect free function.
  It considers a workflow like this:

    - instance is created.
    - later it can be provided with its input.
    - any time a message can be receive.
    - any of the functions returns a list of messages for other peers and possibly an output.
    - it is assumed that the algorithm will provide a single output.

  Messages sent to itself is re-routed to the implementation by this module.
  """

  @type msgs() :: %{(peer :: any()) => [msg :: any()]}
  @type ret(obj) :: {:ok, obj, msgs(), output :: any()}
  @type option() :: {:process_own, boolean()}

  @callback handle_new(arg :: any()) :: ret(obj) when obj: any()
  @callback handle_input(obj, input :: any()) :: ret(obj) when obj: any()
  @callback handle_message(obj, message :: any()) :: ret(obj) when obj: any()

  @type t(obj) :: %GPA{
          mod: module(),
          obj: obj,
          me: any,
          process_own: boolean()
        }
  @enforce_keys [:mod, :obj, :me]
  defstruct mod: nil, obj: nil, me: nil, process_own: true

  ### ==========================================================================
  ### API.
  ### ==========================================================================

  @doc """
  Create new instance of the algorithm.

  Options:
    - process_own can be set to false, if you want to delegate processing of
      self-messages to the upper algorithm, e.g. you compose a node of several roles.
  """
  @spec new(module(), any(), any(), [option()]) :: ret(t(any()))
  def new(mod, me, arg, opts \\ []) do
    {:ok, obj, _msgs, _output} = ret = mod.handle_new(arg)
    gpa = %GPA{mod: mod, obj: obj, me: me, process_own: Keyword.get(opts, :process_own, true)}
    handle_result(gpa, ret)
  end

  @spec input(t(obj), any()) :: ret(t(obj)) when obj: any()
  def input(gpa = %GPA{mod: mod, obj: obj}, input) do
    handle_result(gpa, mod.handle_input(obj, input))
  end

  @spec message(t(obj), any()) :: ret(t(obj)) when obj: any()
  def message(gpa = %GPA{mod: mod, obj: obj}, message) do
    handle_result(gpa, mod.handle_message(obj, message))
  end

  @doc """
  Returns the identified of this (the current) node.
  """
  @spec me(t(obj)) :: any() when obj: any()
  def me(%GPA{me: me}), do: me

  @spec merge(msgs(), any(), ret(obj)) :: ret(obj) when obj: any()
  def merge(prev_msgs, prev_output, {:ok, obj, msgs, output}) do
    merged_msgs = merge_msgs(prev_msgs, msgs)
    merged_output = merge_output(prev_output, output)
    {:ok, obj, merged_msgs, merged_output}
  end

  @doc """
  Merge the message sets and that's it.
  """
  @spec merge_msgs(msgs(), msgs()) :: msgs()
  def merge_msgs(msgs, new_msgs) do
    Map.merge(msgs, new_msgs, fn _, m1, m2 -> m1 ++ m2 end)
  end

  @doc """
  Output can only be set, but not changed.
  """
  @spec merge_output(output | nil, output | nil) :: output | nil when output: any()
  def merge_output(nil, new_output), do: new_output
  def merge_output(output, nil), do: output
  def merge_output(output, output), do: output

  ### ==========================================================================
  ### Helper functions.
  ### ==========================================================================

  @spec handle_result(t(obj), ret(any())) :: ret(t(obj)) when obj: any()
  defp handle_result(gpa = %GPA{me: me, process_own: process_own}, {:ok, obj, msgs, output}) do
    gpa = %{gpa | obj: obj}

    case msgs do
      %{^me => my_msgs} when process_own ->
        acc_init = {:ok, gpa, Map.delete(msgs, me), output}

        Enum.reduce(my_msgs, acc_init, fn msg, {:ok, acc_gpa, acc_msgs, acc_output} ->
          {:ok, new_gpa, new_msgs, new_output} = message(acc_gpa, msg)
          merged_msgs = merge_msgs(acc_msgs, new_msgs)
          merged_output = merge_output(acc_output, new_output)
          {:ok, new_gpa, merged_msgs, merged_output}
        end)

      %{} ->
        {:ok, gpa, msgs, output}
    end
  end

  ### ==========================================================================
  ### Test support functions.
  ### ==========================================================================

  def combined_new(mod, peers) do
    {peers, msgs, outs} =
      Enum.reduce(peers, {%{}, %{}, %{}}, fn {peer_id, arg}, acc ->
        {acc_peers, acc_msgs, acc_outs} = acc
        {:ok, obj, msgs, output} = GPA.new(mod, peer_id, arg)
        acc_peers = Map.put(acc_peers, peer_id, obj)
        acc_msgs = merge_msgs(acc_msgs, msgs)
        acc_outs = Map.put(acc_outs, peer_id, output)
        {acc_peers, acc_msgs, acc_outs}
      end)

    combined_process_msgs(peers, msgs, outs)
  end

  def combined_input(peers, inputs, init_outs \\ %{}) do
    {peers, msgs, outs} =
      Enum.reduce(inputs, {peers, %{}, init_outs}, fn {peer_id, peer_input}, acc ->
        {acc_peers, acc_msgs, acc_outs} = acc
        {:ok, obj, msgs, output} = GPA.input(acc_peers[peer_id], peer_input)
        acc_peers = Map.put(acc_peers, peer_id, obj)
        acc_msgs = merge_msgs(acc_msgs, msgs)
        acc_outs = Map.put(acc_outs, peer_id, output)
        {acc_peers, acc_msgs, acc_outs}
      end)

    combined_process_msgs(peers, msgs, outs)
  end

  defp combined_process_msgs(peers, msgs, outputs) when map_size(msgs) == 0 do
    {:ok, peers, outputs}
  end

  defp combined_process_msgs(peers, msgs, outputs) do
    [{rcp_index, rcp_msgs}] = Enum.take_random(msgs, 1)

    case rcp_msgs do
      [] ->
        combined_process_msgs(peers, Map.delete(msgs, rcp_index), outputs)

      _ ->
        [msg] = Enum.take_random(rcp_msgs, 1)
        msgs = Map.put(msgs, rcp_index, rcp_msgs -- [msg])
        {:ok, new_peer, new_msgs, new_output} = GPA.message(peers[rcp_index], msg)
        peers = Map.put(peers, rcp_index, new_peer)
        msgs = merge_msgs(msgs, new_msgs)
        outputs = update_in(outputs, [rcp_index], &merge_output(&1, new_output))
        combined_process_msgs(peers, msgs, outputs)
    end
  end
end
