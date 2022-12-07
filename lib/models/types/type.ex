defmodule Models.Type do
  @moduledoc """
  Module defining a condition for expression
  """
  use TypedStruct

  @type t() ::
          Models.Type.Constant.t()
          | Models.Type.Variable.t()
          | Models.Type.Tuple.t()
          | Models.Type.Struct.t()
          | Models.Type.Map.t()

  @callback parse_type(any(), any()) :: Models.Type.t()
  @callback has_constant(Models.Type.t()) :: boolean()

  @spec parse_argument_types(any(), String.t(), Integer.t()) :: Models.Type.t()
  def parse_argument_types(argument_ast, fn_name, arg_number) do
    argument = parse_type(argument_ast)

    if argument.name == nil or String.starts_with?(Atom.to_string(argument.name), "_") do
      named_argument = %{argument | name: String.to_atom("#{fn_name}_arg_#{arg_number}")}
      named_argument
    else
      argument
    end
  end

  @spec parse_type(any()) :: Models.Type.t()
  def parse_type(argument_ast)
      when is_atom(argument_ast) or is_number(argument_ast) or is_binary(argument_ast),
      do: Models.Type.Constant.parse_type(argument_ast, %{name: nil})

  def parse_type({argument_ast, _, nil}) do
    Models.Type.Variable.parse_type(argument_ast, nil)
  end

  def parse_type({:%{}, _, argument_ast}) do
    Models.Type.Map.parse_type(argument_ast, %{name: nil})
  end

  def parse_type({:=, _, [{name, _, nil}, {:%{}, _, argument_ast}]}) do
    Models.Type.Map.parse_type(argument_ast, %{name: name})
  end

  def parse_type({:%, _, argument_ast}) do
    Models.Type.Struct.parse_type(argument_ast, %{name: nil})
  end

  def parse_type({:=, _, [{name, _, nil}, {:%, _, argument_ast}]}) do
    Models.Type.Struct.parse_type(argument_ast, %{name: name})
  end

  def parse_type({:{}, _, argument_ast}) do
    Models.Type.Tuple.parse_type(argument_ast, %{name: nil})
  end

  def parse_type({:=, _, [{name, _, nil}, argument_ast]}) do
    Models.Type.Tuple.parse_type(Tuple.to_list(argument_ast), %{name: name})
  end

  def parse_type(argument_ast) when is_list(argument_ast) do
    Models.Type.Tuple.parse_type(argument_ast, %{name: nil})
  end

  def parse_type(argument_ast) do
    Models.Type.Tuple.parse_type(Tuple.to_list(argument_ast), %{name: nil})
  end

  @spec get_arguments_with_constants(List[Models.Type.t()]) :: List[Models.Type.t()]
  def get_arguments_with_constants(arguments) do
    {_, arguments_with_constants} =
      arguments
      |> Enum.map_reduce([], fn argument, acc ->
        has_constant =
          case argument.__struct__ do
            Models.Type.Constant -> Models.Type.Constant.has_constant(argument)
            Models.Type.Map -> Models.Type.Map.has_constant(argument)
            Models.Type.Struct -> Models.Type.Struct.has_constant(argument)
            Models.Type.Tuple -> Models.Type.Tuple.has_constant(argument)
            Models.Type.Variable -> Models.Type.Variable.has_constant(argument)
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

  @spec is_input_argument(String.t(), List[Models.Type.t()]) :: boolean()
  def is_input_argument(var_name, fn_inputs) do
    fn_inputs
    |> Enum.map(fn fn_input -> is_defined_in_argument(var_name, fn_input) end)
    |> Enum.any?(fn x -> x == true end)
  end

  @spec is_defined_in_argument(String.t(), Models.Type.t()) :: boolean()
  defp is_defined_in_argument(var_name, fn_input = %Models.Type.Constant{}),
    do: var_name == fn_input.name

  defp is_defined_in_argument(var_name, fn_input = %Models.Type.Variable{}),
    do: var_name == fn_input.name

  defp is_defined_in_argument(var_name, fn_input = %Models.Type.Map{}) do
    fn_input.key_value_pairs
    |> Enum.map(fn {name, value} ->
      case var_name == name do
        true -> true
        false -> is_defined_in_argument(var_name, value)
      end
    end)
    |> Enum.any?(fn x -> x == true end)
  end

  defp is_defined_in_argument(var_name, fn_input = %Models.Type.Struct{}) do
    case var_name == fn_input.name do
      true -> true
      false -> is_defined_in_argument(var_name, fn_input.arguments)
    end
  end

  defp is_defined_in_argument(var_name, fn_input = %Models.Type.Tuple{}) do
    case var_name == fn_input.name do
      true ->
        true

      false ->
        fn_input.arguments
        |> Enum.map(fn {_, value} ->
          case var_name == value.name do
            true -> true
            false -> is_defined_in_argument(var_name, value)
          end
        end)
        |> Enum.any?(fn x -> x == true end)
    end
  end
end
