# Elixir → TLA<sup>+</sup> Converter

This is a Elixir → TLA<sup>+</sup> Converter created for the Master's degree.

It leverages PlusCal as an intermediate language for easier and more developer-friendly translation rules.

## Usage

1. Add `TLA2TOOLSDIR` environmental variable, containing the directory of `tla2tools.jar` (e.g. `C:\TLA+\toolbox\`).
2. Annotate the translated functions with `@tlagen_function` and the function name (e.g. [here](https://github.com/DeividasBrazenas/tla-generator/blob/d688c0d2e3cc60852a7c5fca0bcdb4c396b2f6ec/test/apps/bracha/lib/rbc_bracha.ex#L147)).
3. Define the specification generation configuration, which should be named after the module name with a `tlagen.json` extension (e.g. [here](https://github.com/DeividasBrazenas/tla-generator/blob/main/test/apps/bracha/lib/rbc_bracha.tlagen.json)). Generated functions should be referenced by names, defined in the step 2.
4. Build the Elixir program. Conversion to TLA<sup>+</sup> will be done automatically and model checking will be launched (initially it will fail due to the model checking configuration files missing - please define them manually, next to the generated specifications).
