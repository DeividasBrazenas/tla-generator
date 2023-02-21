defmodule Verifiers.PlusCal.Test do
  use ExUnit.Case

  test "verifier" do
    function_name = "handle_ready_message"

    file_path =
      "C:\\University\\Master's Thesis\\tla-generator\\test\\tlagen\\priv\\#{function_name}.tla"

    code = Verifier.PluscalConverter.convert_to_code(file_path, "Generated.HandleReadyMessage", "handle_message")

    # {:ok, ast} = Code.string_to_quoted(Enum.join(code, "\r\n"))

    result_path = "C:\\University\\Master's Thesis\\tla-generator\\test\\apps\\bracha\\lib\\rbc_bracha_specs\\#{function_name}\\#{function_name}.ex"

    File.mkdir_p!(Path.dirname(result_path))
    File.write!(result_path, Enum.join(code, "\n"))
  end


  # test "expression" do
  #   lines = [
  #     "broadcaster := rbc.broadcaster;",
  #     "me := rbc.me;",
  #     "output := rbc.output;",
  #     "peers := rbc.peers;",
  #     "propose_sent := rbc.propose_sent;",
  #     "",
  #     "if broadcaster /= me then",
  #     "  goto Done;",
  #     "end if;",
  #     "after_pin_0:",
  #     "",
  #     "if propose_sent /= FALSE then",
  #     "  goto Done;",
  #     "end if;",
  #     "after_pin_1:",
  #     "",
  #     "rbc.propose_sent := TRUE;",
  #     "",
  #     "msgs := [peer_id \\in peers |-> msgs[peer_id] \\cup {<<\"PROPOSE\", me, input>>}];",
  #     "",
  #     "result := <<\"ok\", rbc, msgs, output>>;",
  #     ""
  #   ]

  #   code = Verifier.Expressions.Expression.convert(lines, 0)

  #   IO.inspect(code)
  # end

  # test "ast" do
  #   file_path =
  #     "C:\\University\\Master's Thesis\\tla-generator\\test\\apps\\bracha\\lib\\rbc_bracha_handle_input.ex"

  #   {_, ast} =
  #     file_path
  #     |> File.read!()
  #     |> Code.string_to_quoted()

  #   x =
  #     Macro.to_string(
  #       {:=, [line: 11],
  #        [
  #          {:rbc, [line: 11], nil},
  #          {:%{}, [line: 11], [{:|, [line: 11], [{:rbc, [line: 11], nil}, [propose_sent: true]]}]}
  #        ]}
  #     )

  #   IO.inspect(ast)
  # end
end
