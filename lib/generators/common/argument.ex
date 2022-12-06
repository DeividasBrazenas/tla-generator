defmodule Generators.Common.Argument do
  # Returns arguments from a clause that has all arguments
  @spec get_arguments(List[Models.Function.Clause.t()]) :: List[atom()]
  def get_arguments(clauses) do
    clause_with_all_arguments =
      clauses
      |> Enum.filter(fn c -> !Enum.any?(c.metadata.arguments, fn arg -> arg === :_ end) end)
      |> Enum.at(0)

    clause_with_all_arguments.metadata.arguments
  end

  @spec get_argument_names(Models.Function.t(), String.t()) :: List[String.t()]
  def get_argument_names(function, prefix) do
    arguments_count = length(function.spec.argument_types)

    {_, func_argument_names} =
      Enum.to_list(1..arguments_count)
      |> Enum.map_reduce([], fn arg_number, acc ->
        argument_name = get_argument_name(function.clauses, function.spec.name, arg_number)
        {arg_number, acc ++ ["#{prefix}#{argument_name}"]}
      end)

    func_argument_names
  end

  @spec get_argument_name(List[Models.Function.Clause.t()], String.t(), Integer.t()) :: String.t()
  def get_argument_name(clauses, fn_name, argument_index) do
    {_, name} =
      clauses
      |> Enum.map_reduce(nil, fn clause, _ ->
        argument = Enum.at(clause.metadata.arguments, argument_index - 1)

        argument_name = argument.name

        if argument_name != nil and
             !String.starts_with?(Atom.to_string(argument_name), "#{fn_name}_arg_") do
          {clause, argument_name}
        else
          {clause, nil}
        end
      end)

    if name != nil do
      name
    else
      "#{fn_name}_arg_#{argument_index}"
    end
  end

  @spec generate_tla_string(Models.Argument.t(), String.t(), String.t()) :: List[String.t()]
  def generate_tla_string(argument = %Models.Argument.Constant{}, prefix, accessor) do
    ["#{prefix}#{accessor}#{argument.name} = #{get_constant_value(argument.value)}"]
  end

  def generate_tla_string(argument = %Models.Argument.Tuple{}, prefix, accessor) do
    generated =
      argument.arguments
      |> Enum.with_index(fn arg, idx ->
        generate_tla_string(arg, prefix, "#{accessor}#{argument.name}[#{idx}]")
      end)
      |> Enum.flat_map(fn arg -> arg end)
      |> Enum.filter(fn arg -> arg != "" end)

    generated
  end

  def generate_tla_string(argument = %Models.Argument.Map{}, prefix, accessor) do
    generated =
      argument.key_value_pairs
      |> Enum.map(fn {key, arg} ->
        generate_tla_string(arg, prefix, "#{accessor}#{argument.name}[\"#{key}\"]")
      end)
      |> Enum.flat_map(fn arg -> arg end)
      |> Enum.filter(fn arg -> arg != "" end)

    generated
  end

  def generate_tla_string(argument = %Models.Argument.Struct{}, prefix, accessor) do
    generated = generate_tla_string(argument.arguments, prefix, "#{accessor}#{argument.name}")

    generated
  end

  @spec get_constant_value(any()) :: String.t()
  def get_constant_value(value) when is_atom(value) or is_binary(value), do: "\"#{value}\""
  def get_constant_value(value) when is_number(value), do: value

  @spec get_pluscal_operator(atom()) :: String.t()
  def get_pluscal_operator(operator) do
    case operator do
      :== -> " = "
      :!= -> " # "
      :< -> "<"
      :> -> ">"
      :<= -> "<="
      :>= -> ">="
    end
  end

  @spec get_accessor(String.t(), List[Models.Argument.t()]) ::
          String.t() | nil
  def get_accessor(var_name, fn_inputs) do
    fn_inputs
    |> Enum.map(fn fn_input -> get_accessor_from_input(var_name, fn_input, "") end)
    |> Enum.find(nil, fn accessor -> accessor != nil end)
  end

  @spec get_accessor_from_input(String.t(), Models.Argument.t(), String.t()) ::
          String.t() | nil
  defp get_accessor_from_input(var_name, fn_input = %Models.Argument.Constant{}, prefix) do
    case var_name == fn_input.name do
      true -> "#{prefix}#{fn_input.name}"
      false -> nil
    end
  end

  defp get_accessor_from_input(var_name, fn_input = %Models.Argument.Variable{}, prefix) do
    case var_name == fn_input.name do
      true -> "#{prefix}#{fn_input.name}"
      false -> nil
    end
  end

  defp get_accessor_from_input(var_name, fn_input = %Models.Argument.Map{}, prefix) do
    fn_input.key_value_pairs
    |> Enum.map(fn {name, value} ->
      case var_name == name do
        true -> "#{prefix}#{name}"
        false -> get_accessor_from_input(var_name, value, prefix)
      end
    end)
    |> Enum.find(nil, fn accessor -> accessor != nil end)
  end

  defp get_accessor_from_input(var_name, fn_input = %Models.Argument.Struct{}, prefix) do
    case var_name == fn_input.name do
      true -> "#{prefix}#{fn_input.name}"
      false -> get_accessor_from_input(var_name, fn_input.arguments, "#{prefix}#{fn_input.name}")
    end
  end

  defp get_accessor_from_input(var_name, fn_input = %Models.Argument.Tuple{}, prefix) do
    case var_name == fn_input.name do
      true ->
        "#{prefix}#{fn_input.name}"

      false ->
        fn_input.arguments
        |> Enum.map(fn {number, value} ->
          case var_name == value.name do
            true ->
              "#{prefix}#{fn_input.name}[#{number}]"

            false ->
              get_accessor_from_input(var_name, value, "#{prefix}#{fn_input.name}[#{number}]")
          end
        end)
        |> Enum.find(nil, fn accessor -> accessor != nil end)
    end
  end
end
