# The proving benchmarks join only under BENCH=1.
bench = if System.get_env("BENCH") == "1", do: [Examples.EBench], else: []

for module <-
      [
        Examples.EQuery,
        Examples.EProgramSpace,
        Examples.EUser,
        Examples.EUair,
        Examples.EFace,
        Examples.ELog,
        Examples.EAst,
        Examples.EFacts,
        Examples.EDoubling,
        Examples.EPipeline,
        Examples.ERefusal,
        Examples.EAl,
        Examples.EAlloc,
        Examples.EPhi,
        Examples.ENodes,
        Examples.ESudoku,
        Examples.EPassed,
        Examples.EFol,
        Examples.EForgery,
        Examples.EVerifier
      ] ++ bench do
  Module.create(
    Module.concat(module, Test),
    quote(do: use(ExExample.ExUnit, for: unquote(module))),
    __ENV__
  )
end
