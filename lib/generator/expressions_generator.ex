defmodule Generator.Expressions do
  @spec generate_process_expressions(any(), Integer.t()) ::
          {List[String.t()], List[String.t()], List[String.t()]}
  def generate_process_expressions(
        {:def, _, [{_function_name, _, arguments_ast}, [do: {:__block__, [], body_ast}]]},
        indent_lvl
      ) do
    arguments_condition = Expressions.ArgumentCondition.parse(arguments_ast, indent_lvl)

    {lines, variables, definitions, _} = generate_expressions(body_ast, indent_lvl)

    {arguments_condition ++ lines, variables, definitions}
  end

  @spec generate_expressions(List[any()], Integer.t()) ::
          {List[String.t()], List[String.t()], List[String.t()], Integer.t()}
  def generate_expressions(body_ast, indent_lvl) do
    {lines, variables, definitions, labels_count, _expressions_counter} =
      body_ast
      |> Enum.reduce({[], [], [], 0, %{}}, fn expression_ast,
                                              {lines_acc, variables_acc, definitions_acc,
                                               labels_count_acc, expressions_counter} ->
        expression =
          generate_expression(
            expression_ast,
            expressions_counter,
            %{is_single_line: true},
            indent_lvl
          )

        %Expression{
          name: expression_name,
          lines: lines,
          variables: variables,
          definitions: definitions,
          labels_count: labels_count
        } = expression

        expression_count = Map.get(expressions_counter, expression_name, 0)
        expressions_counter = Map.put(expressions_counter, expression_name, expression_count + 1)

        {lines_acc ++ lines ++ [""], variables_acc ++ variables, definitions_acc ++ definitions,
         labels_count_acc + labels_count, expressions_counter}
      end)

    {lines, Enum.uniq(variables), definitions, labels_count}
  end

  @spec generate_expression(any(), Map.t(), Map.t(), Integer.t()) :: Expression.t()
  def generate_expression(nil, _, _, _) do
    Expressions.Nil.parse()
  end

  def generate_expression(arg, _, _, _)
      when is_boolean(arg) do
    Expressions.Boolean.parse(arg)
  end

  def generate_expression(arg, _, _, _)
      when is_atom(arg) do
    Expressions.Atom.parse(arg)
  end

  def generate_expression(arg, _, _, _)
      when is_number(arg) do
    Expressions.Number.parse(arg)
  end

  def generate_expression({arg, _, nil}, _, _, _) do
    Expressions.Variable.parse(arg)
  end

  def generate_expression({:%{}, _, []}, _, _, _) do
    Expressions.EmptyMap.parse()
  end

  def generate_expression({:==, _, [left_ast, right_ast]}, _, _, _) do
    Expressions.MathSign.parse(left_ast, right_ast, :==)
  end

  def generate_expression({:<, _, [left_ast, right_ast]}, _, _, _) do
    Expressions.MathSign.parse(left_ast, right_ast, :<)
  end

  def generate_expression({:>, _, [left_ast, right_ast]}, _, _, _) do
    Expressions.MathSign.parse(left_ast, right_ast, :>)
  end

  def generate_expression({:<=, _, [left_ast, right_ast]}, _, _, _) do
    Expressions.MathSign.parse(left_ast, right_ast, :<=)
  end

  def generate_expression({:>=, _, [left_ast, right_ast]}, _, _, _) do
    Expressions.MathSign.parse(left_ast, right_ast, :>=)
  end

  def generate_expression({:+, _, [left_ast, right_ast]}, _, _, _) do
    Expressions.MathSign.parse(left_ast, right_ast, :+)
  end

  def generate_expression({:-, _, [left_ast, right_ast]}, _, _, _) do
    Expressions.MathSign.parse(left_ast, right_ast, :-)
  end

  def generate_expression({:*, _, [left_ast, right_ast]}, _, _, _) do
    Expressions.MathSign.parse(left_ast, right_ast, :*)
  end

  def generate_expression({:/, _, [left_ast, right_ast]}, _, _, _) do
    Expressions.MathSign.parse(left_ast, right_ast, :/)
  end

  def generate_expression({:and, _, [left_ast, right_ast]}, _, _, _) do
    Expressions.MathSign.parse(left_ast, right_ast, :and)
  end

  def generate_expression({:or, _, [left_ast, right_ast]}, _, _, _) do
    Expressions.MathSign.parse(left_ast, right_ast, :or)
  end

  def generate_expression({:not, _, [condition_ast]}, _, _, _) do
    Expressions.Not.parse(condition_ast)
  end

  def generate_expression(
        {:{}, _, arguments_ast},
        expressions_counter,
        options,
        indent_lvl
      ) do
    is_single_line = Map.get(options, :is_single_line, false)

    case is_single_line do
      true -> Expressions.Return.parse(arguments_ast, expressions_counter, indent_lvl)
      false -> Expressions.Tuple.parse(arguments_ast, expressions_counter, indent_lvl)
    end
  end

  def generate_expression(arguments_ast, expressions_counter, options, indent_lvl)
      when is_list(arguments_ast) do
    is_single_line = Map.get(options, :is_single_line, false)

    case is_single_line do
      true -> Expressions.Return.parse(arguments_ast, expressions_counter, indent_lvl)
      false -> Expressions.Tuple.parse(arguments_ast, expressions_counter, indent_lvl)
    end
  end

  def generate_expression(
        {:=, _,
         [{:%, _, [{:__aliases__, _, _}, {:%{}, _, assignments}]}, {src_variable, _, nil}]},
        _,
        _,
        indent_lvl
      ) do
    Expressions.MapDestrucure.parse(Map.new(assignments), src_variable, indent_lvl)
  end

  def generate_expression(
        {:=, _,
         [
           {variable, _, nil},
           {:%, _,
            [
              {:__aliases__, _, [_type]},
              {:%{}, _, [{:|, _, [{src_variable, _, nil}, updates]}]}
            ]}
         ]},
        expressions_counter,
        _,
        indent_lvl
      ) do
    Expressions.MapUpdate.parse(
      variable,
      src_variable,
      Map.new(updates),
      expressions_counter,
      indent_lvl
    )
  end

  def generate_expression(
        {:=, _,
         [
           {new_map_variable, _, nil},
           {{:., _, [{:__aliases__, _, [:Map]}, :put]}, _,
            [{old_map_variable, _, nil}, key, value]}
         ]},
        expressions_counter,
        _,
        indent_lvl
      ) do
    Expressions.MapPut.parse(
      new_map_variable,
      old_map_variable,
      key,
      value,
      expressions_counter,
      indent_lvl
    )
  end

  def generate_expression(
        {:=, _,
         [
           {variable, _, nil},
           {{:., _, [{:__aliases__, _, [:Map]}, :get]}, _,
            [{map_variable, _, nil}, key_ast, default_value_ast]}
         ]},
        _,
        _,
        indent_lvl
      ) do
    Expressions.MapGet.parse(
      variable,
      map_variable,
      key_ast,
      default_value_ast,
      indent_lvl
    )
  end

  def generate_expression(
        {:=, _, [{variable, _, nil}, {:map_size, _, [{argument, _, nil}]}]},
        _,
        _,
        indent_lvl
      ) do
    Expressions.MapSize.parse(
      variable,
      argument,
      indent_lvl
    )
  end

  def generate_expression(
        {:=, _, [{:^, _, [{left_operand, _, nil}]}, right_operand_ast]},
        expressions_counter,
        _,
        indent_lvl
      ) do
    Expressions.Pin.parse(
      left_operand,
      right_operand_ast,
      expressions_counter,
      indent_lvl
    )
  end

  def generate_expression(
        {:=, _,
         [
           {variable, _, nil},
           {{:., _, [{:__aliases__, _, [:Enum]}, :into]}, _,
            [
              {enumerable, _, nil},
              {:%{}, _, []},
              {:fn, _, [{:->, _, [[iterator], action]}]}
            ]}
         ]},
        _,
        _,
        indent_lvl
      ) do
    Expressions.EnumInto.parse(
      variable,
      enumerable,
      iterator,
      action,
      indent_lvl
    )
  end

  def generate_expression(
        {:if, _, [condition, [do: {:__block__, [], do_ast}, else: {:__block__, [], else_ast}]]},
        expressions_counter,
        _,
        indent_lvl
      ) do
    Expressions.IfStatement.parse(condition, do_ast, else_ast, expressions_counter, indent_lvl)
  end

  def generate_expression(
        {:=, _, [{variable, _, nil}, {:cond, _, [[do: conditions_ast]]}]},
        _,
        _,
        indent_lvl
      ) do
    Expressions.Cond.parse(variable, conditions_ast, indent_lvl)
  end

  def generate_expression(
        {:=, _, [{variable, _, nil}, {:%{}, _, []}]},
        _,
        _,
        _
      ) do
    Expressions.DefaultValueAssignment.parse(variable)
  end

  def generate_expression(
        {{:., _, [{:predicate, _, nil}]}, _, [arguments_ast]},
        _,
        _,
        _
      ) do
    Expressions.CustomPredicateCall.parse(arguments_ast)
  end

  def generate_expression(ast, _, _, _) do
    IO.inspect(ast)
    %Expression{name: :not_implemented, lines: ["not implemented"]}
  end
end
