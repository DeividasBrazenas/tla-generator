defmodule TlaGeneratorV2.MixProject do
  use Mix.Project

  def project do
    [
      app: :tla_generator_v2,
      version: "0.1.0",
      elixir: "~> 1.14",
      start_permanent: Mix.env() == :prod,
      deps: deps()
    ]
  end

  # Run "mix help compile.app" to learn about applications.
  def application do
    [
      extra_applications: [:logger]
    ]
  end

  # Run "mix help deps" to learn about dependencies.
  defp deps do
    [
      {:typed_struct, "~> 0.2.1"},
      {:poison, "~> 5.0"},
      # {:bracha, path: "test/apps/bracha"}
    ]
  end
end
