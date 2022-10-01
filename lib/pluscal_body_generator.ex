defmodule PlusCal.Generator.Body do
  @spec get(String.t(), List[atom()], any()) :: List[String.t()]
  def get(module_name, generation_defs, ast) do
    specs =
      Tla.Generator.Models.Function.Spec.get(ast)
      |> Enum.filter(fn spec -> Enum.member?(generation_defs, spec.name) end)

    functions = Tla.Generator.Models.Function.get(specs, ast)
    IO.inspect(functions)

    body =
      [get_extensions(specs)] ++
        [get_constants(functions)] ++
        get_algorithm(module_name, functions)

    IO.inspect(body)
    body
  end

  @spec get_extensions(List[Tla.Generator.Models.Function.Spec.t()]) :: String.t()
  defp get_extensions(specs) do
    extensions =
      specs
      |> Enum.map(fn spec ->
        cond do
          spec.return_type === :integer -> "Naturals"
        end
      end)
      |> Enum.uniq()

    # For PlusCal
    extensions = extensions ++ ["Sequences"]

    if length(extensions) > 0 do
      "EXTENDS #{Enum.join(extensions, ", ")}"
    else
      ""
    end
  end

  @spec get_constants(List[Tla.Generator.Models.Function.t()]) :: String.t()
  defp get_constants(funcs) do
    arguments =
      funcs
      |> Enum.flat_map(fn func ->
        func.arguments
      end)
      |> Enum.uniq()
      |> Enum.map(fn argument -> "in_#{argument}" end)

    if length(arguments) > 0 do
      "CONSTANTS #{Enum.join(arguments, ", ")}"
    else
      ""
    end
  end

  @spec get_algorithm(String.t(), List[Tla.Generator.Models.Function.t()]) :: List[String.t()]
  defp get_algorithm(module_name, funcs) do
    algorithm =
      [get_algorithm_header(module_name)] ++
        [""] ++
        [get_algorithm_variables(funcs)] ++
        [""] ++
        get_algorithm_procedures(funcs) ++
        [""] ++
        get_algorithm_body(funcs) ++
        [get_algorithm_footer()]

    algorithm
  end

  @spec get_algorithm_variables(List[Tla.Generator.Models.Function.t()]) :: List[String.t()]
  defp get_algorithm_variables(funcs) do
    funcs_with_result =
      funcs
      |> Enum.filter(fn func -> func.spec.return_type != nil end)
      |> Enum.map(fn func -> "result_#{func.spec.name}" end)
      |> Enum.uniq()

    if length(funcs_with_result) > 0 do
      "variables #{Enum.join(funcs_with_result, ", ")}"
    else
      ""
    end
  end

  @spec get_algorithm_procedures(List[Tla.Generator.Models.Function.t()]) :: List[String.t()]
  defp get_algorithm_procedures(funcs) do
    procedures =
      funcs
      |> Enum.flat_map(fn func -> get_algorithm_procedure(func) ++ [""] end)
    IO.inspect(procedures)
    procedures
  end

  @spec get_algorithm_procedure(Tla.Generator.Models.Function.t()) :: List[String.t()]
  defp get_algorithm_procedure(
         %Tla.Generator.Models.Function{spec: spec, arguments: arguments, cases: cases}
       ) do

    procedure =
      ["procedure generated_#{spec.name}(#{Enum.join(arguments, ", ")})"] ++
        ["begin"] ++
        ["generated_#{spec.name}:"] ++
        get_algorithm_procedure_body(spec.name, cases) ++
        ["return;"] ++
        ["end procedure;"]

    procedure
  end

  @spec get_algorithm_procedure_body(String.t(), List[Tla.Generator.Models.Function.Case.t()]) ::
          List[String.t()]
  defp get_algorithm_procedure_body(fn_name, cases) do
    if_cases = cases |> Enum.filter(fn c -> !c.condition.is_negated end)
    negated_cases = cases |> Enum.filter(fn c -> c.condition.is_negated end)

    body =
      Enum.map(if_cases, fn c ->
        [
          "if #{c.condition.left_operand} #{c.condition.operator} #{c.condition.right_operand} then"
        ] ++
          ["  result_#{fn_name} := #{c.return};"]
      end) ++
        Enum.map(negated_cases, fn c ->
          ["else"] ++
            ["  result_#{fn_name} := #{c.return};"]
        end) ++
        ["end if;"]

    List.flatten(body)
  end

  @spec get_algorithm_body(List[Tla.Generator.Models.Function.t()]) :: List[String.t()]
  defp get_algorithm_body(funcs) do
    body =
      ["begin"] ++
        Enum.map(funcs, fn func ->
          ["#{func.spec.name}:"] ++
            ["  if result_#{func.spec.name} = defaultInitValue then"] ++
            [
              "    call generated_#{func.spec.name}(#{Enum.join(Enum.map(func.arguments, fn argument -> "in_#{argument}" end), ", ")})"
            ] ++
            ["  end if;"]
        end)

    List.flatten(body)
  end

  @spec get_algorithm_header(String.t()) :: String.t()
  defp get_algorithm_header(module_name) do
    "(*--algorithm #{module_name}"
  end

  @spec get_algorithm_footer() :: String.t()
  defp get_algorithm_footer() do
    "end algorithm; *)"
  end
end
