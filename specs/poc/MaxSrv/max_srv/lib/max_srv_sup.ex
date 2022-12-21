defmodule MaxSrv.Sup do
  def start_link() do
    Supervisor.start_link([%{:id => :main, :start => {MaxSrv, :start_link, []}}],
      strategy: :one_for_one
    )
  end
end
