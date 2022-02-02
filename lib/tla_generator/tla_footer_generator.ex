defmodule TlaFooterGenerator do
  def getFooter(moduleName) do
    length = 33 + 33 + 6 + 3 + String.length(moduleName)
    String.duplicate("=", length)
  end
end
