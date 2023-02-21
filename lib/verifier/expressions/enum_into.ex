defmodule Verifier.Expressions.EnumInto do
  alias Common.Indent, as: Indent

  def convert(variable, enumerable, iterator, action, indent_lvl) do
    action_code = convert_action(action)
    code = "#{Indent.build(indent_lvl)}#{variable} = Enum.into(#{enumerable}, %{}, fn #{iterator} -> #{action_code} end)"

    code
  end

  def convert_action(action) do
    cond do
      (key_value_regex = Regex.run(~r/^([^\[]+)\[([^\]]+)] \\cup {(.*)}$/, action)) ->
        key = Enum.at(key_value_regex, 2)
        value = Verifier.Helpers.map_type(Enum.at(key_value_regex, 3))
        code = "{#{key}, [#{value}]}"
        code

      true -> ""
    end
  end
end


# msgs := [peer_id \in peers |-> msgs[peer_id] \cup {<<"PROPOSE", me, input>>}];
# msgs = Enum.into(peers, %{}, fn peer_id -> {peer_id, [{:PROPOSE, me, input}]} end)
