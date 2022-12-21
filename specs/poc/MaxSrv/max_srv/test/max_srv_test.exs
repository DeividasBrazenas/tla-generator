defmodule MaxSrvTest do
  use ExUnit.Case

  test "max" do
    {:ok, pid} = MaxSrv.start_link()
    assert 29 == MaxSrv.max(pid, [17, 13, 29, 7])
  end
end
