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
  @callback has_constant(Models.Argument.t()) :: boolean()

  @spec parse_function_argument(any(), Integer.t()) :: Models.Argument.t()
  def parse_function_argument(argument_ast, arg_number) do
    argument = parse_argument(argument_ast)

    if argument.name == nil or String.starts_with?(Atom.to_string(argument.name), "_") do
      named_argument =
        case argument.__struct__ do
          Models.Argument.Constant ->
            %Models.Argument.Constant{argument | name: String.to_atom("arg_#{arg_number}")}

          Models.Argument.Map ->
            %Models.Argument.Map{argument | name: String.to_atom("arg_#{arg_number}")}

          Models.Argument.Struct ->
            %Models.Argument.Struct{argument | name: String.to_atom("arg_#{arg_number}")}

          Models.Argument.Tuple ->
            %Models.Argument.Tuple{argument | name: String.to_atom("arg_#{arg_number}")}

          Models.Argument.Variable ->
            %Models.Argument.Variable{argument | name: String.to_atom("arg_#{arg_number}")}
        end

      named_argument
    else
      argument
    end
  end

  @spec parse_argument(any()) :: Models.Argument.t()
  def parse_argument(argument_ast)
      when is_atom(argument_ast) or is_number(argument_ast) or is_binary(argument_ast),
      do: Models.Argument.Constant.parse_argument(argument_ast, %{name: nil})

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

  @spec get_arguments_with_constants(List[Models.Argument.t()]) :: List[Models.Argument.t()]
  def get_arguments_with_constants(arguments) do
    {_, arguments_with_constants} =
      arguments
      |> Enum.map_reduce([], fn argument, acc ->
        has_constant =
          case argument.__struct__ do
            Models.Argument.Constant -> Models.Argument.Constant.has_constant(argument)
            Models.Argument.Map -> Models.Argument.Map.has_constant(argument)
            Models.Argument.Struct -> Models.Argument.Struct.has_constant(argument)
            Models.Argument.Tuple -> Models.Argument.Tuple.has_constant(argument)
            Models.Argument.Variable -> Models.Argument.Variable.has_constant(argument)
            _ -> false
          end

        if has_constant do
          {argument, acc ++ [argument]}
        else
          {argument, acc}
        end
      end)

    arguments_with_constants
  end
end
