# TlaGenerator

**TODO: Add description**

## Installation

If [available in Hex](https://hex.pm/docs/publish), the package can be installed
by adding `tla_generator` to your list of dependencies in `mix.exs`:

```elixir
def deps do
  [
    {:tla_generator, "~> 0.1.0"}
  ]
end
```

Documentation can be generated with [ExDoc](https://github.com/elixir-lang/ex_doc)
and published on [HexDocs](https://hexdocs.pm). Once published, the docs can
be found at [https://hexdocs.pm/tla_generator](https://hexdocs.pm/tla_generator).

## Notes

  * Consider various approaches to the use of Refinement proofs in the proof of the main algorithm.
    The latter will use the functions as atomic? Or will consider the Done flags or <>[] operators?

  * We have to have a way to abstract some functions (by specifying their properties only, instead
    of their implementations). This probably should be done during the spec extraction. Or maybe
    just references have to be generated? For example to replace Logger calls by TRUE, Kernel
    functions by their properties, etc.

      - Skip them from the spec?

      - Only generate references?

      - Generate properties based on info in code or supplementary tla module?

  * Maybe an example for a refinement with the intermediate <>Spec (with actions instead of
    operators) is a calculation of sum over a set. It can use the Max function generated as
    an FSM.

  * A Rabia, Raft or Paxos implementation can be used as a more elaborated example.

  * See <NOTES.pdf> for an idea of how a refinements could be organized in the case of a
    function translated to an FSM.

  * Consider model checker for verifying the refinements.

  * Non-deterministic functions should be supported as well. Maybe by `\E ...`.

  * Function clause ordering could be modelled by adding inverted conditions
    for all the subsequent clauses.
