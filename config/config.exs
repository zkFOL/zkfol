import Config

# AL keeps its store in the host's cwd; these programs and packages seed a fresh image.
config :al,
  transaction_programs: [:bootstrap, :package_system],
  package_channels: [{:builtin, {:priv, "packages"}}],
  package_environment: [:elixir_process, :mapset, :interval, :constraints]

# AL's MCP server sits off its 3031 default: 3030 next door is the GT MCP server.
config :al, AL.MCP, port: 3033

# Tests keep their own store, apart from a live node's log, and serve nothing.
if config_env() == :test do
  System.put_env("AL_MNESIA_DISTRIBUTED", "false")
  config :al, mnesia_dir: ".mnesiastore-test/"
  config :al, AL.MCP, enabled: false
end
