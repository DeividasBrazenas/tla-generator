defmodule TlaHeaderGenerator do
  def getHeader(moduleName) do
    tlaValue = "#{String.duplicate("-", 33)} MODULE #{moduleName} #{String.duplicate("-", 33)}"
    tlaValue
  end
end
