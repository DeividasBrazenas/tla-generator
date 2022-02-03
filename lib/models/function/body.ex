defmodule Function.Body do
  defstruct [:name, :arguments, :condition, :return]

  def getFunctionBodies(ast) do
    {_, functionBodies} = Macro.postwalk(ast, [], &getFunction/2)
    functionBodies
  end

  defp getFunction({:def, _, func} = node, acc) do
    body = getBody1(func)
    {node, acc ++ [body]}
  end

  defp getFunction(node, acc), do: {node, acc}

  defp getBody1([{:when, _, func}, [do: {return, _, _}]]) do
    body = getBody2(func)
    body = %{body | return: return}
    body
  end

  defp getBody1([func, [do: {return, _, _}]]) do
    body = getBody2(func)
    body = %{body | return: return}
    body
  end

  defp getBody1(node), do: {node}

  defp getBody2([func, cond]) do
    body = getBody2(func)
    condition = getCondition(cond)
    body = %{body | condition: condition}
    body
  end

  defp getBody2({name, _, args}) do
    body = %Function.Body{
      name: name,
      arguments: Enum.map(args, fn {arg, _, _} -> arg end)
    }

    body
  end

  defp getBody2(node), do: {node}

  defp getCondition({operator, _, [{left, _, _}, {right, _, _}]}) do
    condition = %Function.Condition{
      operator: operator,
      left_operand: left,
      right_operand: right
    }

    condition
  end
end
