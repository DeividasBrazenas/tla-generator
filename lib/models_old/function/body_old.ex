defmodule Tla.Generator.Models.Function.BodyOld do
  use TypedStruct

  typedstruct do
    @typedoc "Type for a function body"

    field(:name, atom(), default: nil, enforce: true)
    field(:arguments, List[atom()], default: [])
    field(:condition, Tla.Generator.Models.Function.Condition.t(), default: nil)
    field(:return, atom(), default: nil)
  end

  @spec get(any()) :: List[Tla.Generator.Models.Function.Body.t()]
  def get(ast) do
    IO.inspect(ast)
    {_, bodies} = Macro.postwalk(ast, [], &get_body/2)
    bodies
  end

  @spec get_body(any(), List[Tla.Generator.Models.Function.Body.t()]) ::
          {any(), List[Tla.Generator.Models.Function.Body.t()]}
  defp get_body({:def, _, func} = node, acc) do
    body = get_body_with_return(func)
    {node, acc ++ [body]}
  end

  defp get_body(node, acc), do: {node, acc}

  @spec get_body_with_return(any()) :: List[Tla.Generator.Models.Function.Body.t()]
  defp get_body_with_return([{:when, _, func}, [do: {return, _, _}]]) do
    body = get_inner_body(func)
    body = %{body | return: return}
    body
  end

  defp get_body_with_return([func, [do: {return, _, _}]]) do
    body = get_inner_body(func)
    body = %{body | return: return}
    body
  end

  defp get_body_with_return(node), do: {node}

  @spec get_inner_body(any()) :: List[Tla.Generator.Models.Function.Body.t()]
  defp get_inner_body([func, cond]) do
    IO.inspect(cond)
    body = get_inner_body(func)
    condition = Tla.Generator.Models.Function.Condition.get(cond)
    body = %{body | condition: condition}
    body
  end

  defp get_inner_body({name, _, args}) do
    body = %Tla.Generator.Models.Function.Body{
      name: name,
      arguments: Enum.map(args, fn {arg, _, _} -> arg end)
    }

    body
  end

  defp get_inner_body(node), do: {node}
end
