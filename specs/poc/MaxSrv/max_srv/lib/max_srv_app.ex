defmodule MaxSrv.App do
  use Application

  def start(_mode, _arg) do
    MaxSrv.Sup.start_link()
  end
end
