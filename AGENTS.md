# Zkfol

zkFOL in Elixir: the logic of *Integer SNARKs for First-Order Logic* (Gabbay–Mendelsohn),
arithmetised to a uniform AIR and proved through Zinc+. A single Elixir application
drives the Zinc+ prover **in-process via a Rustler NIF** (not an external runner).

## Conventions (source of truth — read them)

The project's coding and git conventions live as skills in `.claude/skills/`. Read
them; do not rely on paraphrase (they evolve):

- `general-conventions/SKILL.md` — language-agnostic: minimize code, generalize
  don't special-case, dead code is noise, typed cross-module structures, **run
  examples before reviewing**, the anti-patterns (never add scope / single-use
  abstractions / handle impossible errors), the failure protocol.
- `elixir-conventions/SKILL.md` — pattern-match in heads, `with` over nested `case`,
  never nest reduces, map-then-combine over stateful reduce, `typedstruct`, ExExample.
- `git-conventions/SKILL.md` — the topic-branch DAG (base/next/main/maint, one concern
  per topic, base-on/merge, no evil merges, fold fixes to origin).
- `code-review/SKILL.md` — invoked on demand for reviews.

## Build / test / run

- `mix compile` — compiles Elixir + the Rust NIF (`native/zkfol_zinc_plus`, rustler).
  The NIF build is slow; avoid needless recompiles.
- `mix test` — runs the examples as tests (`test/examples_test.exs` wires each
  `Examples.E<Module>` in via `use ExExample.ExUnit`).
- `mix dialyzer` — type check (config in `.dialyzer_ignore.exs`).
- `mix format` — 98-char lines; run before finalizing.
- One-off: `MIX_ENV=test timeout 60 mix run -e 'Examples.EFacts.factorial()'` (never
  `--no-halt`; dev's mnesia store belongs to the live GT node). The test env lands
  every solve on one shared AL branch, so the suite runs in ~2s — run it freely.
- Examples live in `lib/examples/e_<module>.ex`, module `E<Module>`. They are the
  primary verification — **run them, don't reason from signatures**.

## The pipeline (what compiles a statement to a proof)

A `Zkfol.Statement` flows through a `Zkfol.Pipeline` of passes (each `{module, opts}`),
its stage a sum-type — `Raw` → `Derived` → `Solved`. Evaluation needs no Φ and
stops at `Derived`; only proving needs the lowering, which is why it runs last:

- `Zkfol.Lang` — the relational surface: `defrel`/`rel` macros → a predicate (`Ast`).
  As the last pass it lowers the run's relations and lays its derivation on the
  allocation born of that (`Al.relaid`), reaching `Solved`.
- `Zkfol.Al` — the AL backend: runs the statement as clauses, the derivation IS the
  witness (judged by the oracle). `derived/3` is the run half, `relaid/2` the link
  half, `solved/3` both in one call. A free count asks the *question* first — the clauses
  as plain AL (`Al.question/1`), no trace, no size — then the structural ask; refusals
  are typed (`no_answer` is a finite no, `unresolved_within_budget` outran AL's fixed
  reduction budget) and nothing searches by witness size. Predicates that call
  predicates compile to one chain, each column wearing its relation's tag. Surface
  guards (`x > 2`) steer the derivation and compile into the predicate as slack.
  `Zkfol.Facts` reads order-2 descriptors; `Zkfol.Doubling` rewrites recurrences to a
  log-depth kernel.
- `Zkfol.Witness` — runs the statement via `Al.derived`; the derivation is the answer.
- `Zkfol.Uair` — `emit/3` translates a Solved statement to Figure 2 over committed
  columns; `Zkfol.Prover` proves it on Zinc+. Mode is a sum: `Uair.Plain | Composed`
  (`Composed` = Section 4 lowering for unscheduled pointers; its reads prove
  natively on Zinc+'s pointer query).
- `Zkfol` — the front door: `compile/2` / `emit/2`, journalling the whole act.

Cross-cutting: `Zkfol.Ast` (the algebra, Figure 2), `Zkfol.Refusal` (typed refusals —
`{reason, detail}`, never string errors), `Zkfol.Log` (the command log = the only durable
state, mnesia; `application.ex` runs `Log.setup` + the `Prover`), `Zkfol.Interpretation`/
`Semantics` (the witness oracle: an interpretation is Def 2.16's matrix over N, `eval` is
Figure 3 with `:error` for the undefined cell, `valid?/2` the judgement), `Zkfol.ZincPlus`
(the NIF boundary). Machinery ships only with a producer: the BitPoly `Lookup` mode and
`Zkfol.Range` were removed until an emitter exists; their return paths are documented.

`src/` is a **Glamorous Toolkit** Tonel package (live views over a uair, the pipeline as
a graph) that reads the running node over `gt_bridge` — independent of `lib/`.

## Git workflow

The rules live in the git-conventions skill — read it, don't paraphrase it. The
shape in one line: topics form a DAG off `base`, one concern each; `next` is a
rebuildable collector that topics enter only by merge.

## Project-specific notes

- Zinc+ is a cargo git dep on the `mariari/zinc-plus` fork. The trace column wall depends
  on the pinned `PnttConfig`; read `native/zkfol_zinc_plus/src/config.rs` for the current
  limit rather than quoting a number (it moves with the pin).
- `src/` (Glamorous Toolkit) and `lib/` diverge in both directions — some GT work is done in
  the image, some on disk. Never export the image wholesale over the worktree; splice per file.
