defmodule MaxSrv do
  use GenServer

  def start_link(), do: GenServer.start_link(__MODULE__, {})

  def max(ref, items), do: GenServer.call(ref, {:max, items})

  @impl GenServer
  def init({}) do
    {:ok, nil}
  end

  # The implementation intensionally not optimal.
  # We could use Enum.max as well.
  @impl GenServer
  def handle_call({:max, items}, _from, state) do
    [first | others] = items
    max = Enum.reduce(others, first, &Kernel.max(&1, &2))
    {:reply, max, state}
  end
end
