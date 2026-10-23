defmodule Zkfol.MixProject do
  use Mix.Project

  def project do
    [
      app: :zkfol,
      version: "0.6.1",
      elixir: "~> 1.18",
      start_permanent: Mix.env() == :prod,
      dialyzer: [plt_add_apps: [:ex_unit, :crypto, :mnesia]],
      deps: deps()
    ]
  end

  def application do
    [
      mod: {Zkfol.Application, []},
      extra_applications: [:logger, :crypto]
    ]
  end

  defp deps do
    [
      {:ex_example, "~> 0.1.2"},
      {:event_broker, "~> 1.1.1"},
      {:rustler, "~> 0.38.0", runtime: false},
      {:gt_bridge, "~> 0.20.1", override: true},
      {:al, git: "https://merge-base.com/aleph/AL.git", branch: "mariari/al-integration"},
      {:typed_struct, "~> 0.3"},
      {:dialyxir, "~> 1.4", only: [:dev, :test], runtime: false}
    ]
  end
end
