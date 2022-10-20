defmodule Models.Argument do
  @moduledoc """
  Module defining a condition for expression
  """
  use TypedStruct

  @type t() ::
          Models.Argument.Constant.t()
          | Models.Argument.Variable.t()
          | Models.Argument.Tuple.t()
          | Models.Argument.Struct.t()
          | Models.Argument.Map.t()

  @callback parse_argument(any(), any()) :: Models.Argument.t()

  @spec parse_argument(any()) :: Models.Argument.t()
  def parse_argument(argument_ast)
      when is_atom(argument_ast) or is_number(argument_ast) or is_binary(argument_ast),
      do: Models.Argument.Constant.parse_argument(argument_ast, nil)

  def parse_argument({argument_ast, _, nil}) do
    Models.Argument.Variable.parse_argument(argument_ast, nil)
  end

  def parse_argument({:%{}, _, argument_ast}) do
    Models.Argument.Map.parse_argument(argument_ast, %{name: nil})
  end

  def parse_argument({:=, _, [{name, _, nil}, {:%{}, _, argument_ast}]}) do
    Models.Argument.Map.parse_argument(argument_ast, %{name: name})
  end

  def parse_argument({:%, _, argument_ast}) do
    Models.Argument.Struct.parse_argument(argument_ast, %{name: nil})
  end

  def parse_argument({:=, _, [{name, _, nil}, {:%, _, argument_ast}]}) do
    Models.Argument.Struct.parse_argument(argument_ast, %{name: name})
  end

  def parse_argument({:{}, _, argument_ast}) do
    Models.Argument.Tuple.parse_argument(argument_ast, %{name: nil})
  end

  def parse_argument({:=, _, [{name, _, nil}, argument_ast]}) do
    Models.Argument.Tuple.parse_argument(Tuple.to_list(argument_ast), %{name: name})
  end

  def parse_argument(argument_ast) do
    Models.Argument.Tuple.parse_argument(Tuple.to_list(argument_ast), %{name: nil})
  end
end
