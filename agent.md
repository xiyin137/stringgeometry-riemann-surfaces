# Codex Agent Guidance for StringGeometry

This file is the working guidance for Codex in this repository.

## Project development philosophy

1. Keep three clearly separated tracks:
   - `SchemeTheoretic/*`: algebraic/scheme-theoretic development.
   - `Analytic/*`: complex-analytic Riemann-surface development.
   - `GAGA/*`: bridge layer that compares/transfers results between the two.
2. Avoid cross-track leakage:
   - `Analytic/*` should not depend on `SchemeTheoretic/*` or `GAGA/*` internals.
   - `SchemeTheoretic/*` should not depend on `Analytic/*` or `GAGA/*` internals.
   - Cross-track equivalence/transport belongs in `GAGA/*`.
3. When implementing new results, prove them in their native track first; only then add
   bridge statements in `GAGA/*`.
4. Keep TODO/planning notes aligned with this split:
   - one active TODO flow per major track (`SchemeTheoretic`, `Analytic`, `GAGA`),
   - each TODO should include dependency order of key theorems in that track.

## Analytic chart-transition policy (critical)

1. `chartTransition (q r)` is selector-based shorthand for
   `(extChartAt q) ∘ (extChartAt r).symm` under the current `chartAt`/`extChartAt`
   choices; it is not an intrinsic transition determined only by center points.
2. Expressions involving the moving selector `p ↦ chartAt ℂ p`
   (for example derivatives evaluated at `((chartAt ℂ p) p)`) are selector-dependent
   diagnostics, not canonical geometric objects.
3. Never infer manifold non-smoothness from non-regularity of selector-dependent
   expressions; such results only diagnose the current encoding/selection route.
4. For universal/intrinsic theorems, prefer explicit chart-indexed overlap statements
   (`e, e' ∈ atlas`) or chart-free bundle-section formulations, then prove invariance
   under chart change.
5. On `RiemannSphere`, use the explicit two-chart model (`z` and `z' = 1 / z`) for
   concrete computations, and keep this separate from selector-dependent convenience
   definitions.

## Execution priority (current phase)

1. Focus first on deep theorem closure and reusable infrastructure development.
2. Prioritize blockers on the main dependency chain over peripheral modules and cosmetic cleanup.
3. When deep blockers remain, avoid spending cycles on low-impact edits (style-only rewrites, linter-only cleanup, opportunistic side quests) unless explicitly requested.
4. For the analytic track specifically, keep `Jacobian/*`, `Moduli/*`, and `Applications/*` low priority until the RR chain is materially advanced.
5. Each substantial pass should produce one of:
   - a closed deep theorem, or
   - a new reusable infrastructure lemma that unblocks deep theorems, or
   - a precise blocker report with failed attempts and next concrete bridge lemma.
6. Do not hesitate to expand and deepen infrastructure when core proofs are blocked:
   - prefer adding robust bridge lemmas/definitions over repeatedly forcing the same stuck goal,
   - invest in reusable abstractions that shorten multiple downstream proofs,
   - treat "infrastructure debt" payoff as first-class progress.

## Core rigor rules

1. Never introduce `axiom` (or any equivalent assumption-smuggling) in Lean code.
2. Prioritize fully sound definitions and correct theorem statements over quick placeholders.
3. Definitions must be proper and rigorous; avoid semantic stubs that only satisfy types.
4. Avoid fake constructions and placeholder shortcuts (`True := trivial`, unjustified `.choose`, arbitrary junk terms) unless mathematically justified.
5. For unresolved theorem-level obligations, prefer explicit `sorry` at theorem/lemma proof sites over burying missing mathematics in witness fields or bundled assumptions.
6. Never use `sorry` in `def`/`structure`/`abbrev` bodies.
7. Do not "simplify" by weakening or distorting definitions just to make proofs easier.
8. If a proof stalls, first check: (a) statement correctness, (b) definition correctness, (c) missing infrastructure.
9. Do not downgrade theorem statements merely to close goals.
10. Treat type-level issues as high priority; they often indicate bad definitions or missing bridge lemmas.
11. Reuse existing results first: search Mathlib and local `StringGeometry` modules before re-proving.
12. Prefer reusable infrastructure over ad-hoc local hacks.
13. Prefer local infrastructure development first when blocked: add internal lemmas/definitions/bridges before introducing external assumption bundles.
14. If required API/lemmas are missing in Mathlib, explicitly build robust local infrastructure in this repo first:
   - add reusable bridge lemmas in the nearest `Infrastructure/*` or `Helpers/*` module,
   - prefer these local bridges over one-off in-proof workaround scripts,
   - then refactor call sites to consume the new infrastructure.
15. In `WithTop`/`WithBot` goals, annotate `⊤`/`⊥`/`0` and casts explicitly to avoid metavariable-stuck typeclass resolution.

## Sorry-closing workflow

1. Use `sorry` intentionally to mark real theorem/lemma proof gaps during active work.
2. Do not hide proof gaps by inflating structures with assumption-carrying witness fields.
3. Try hard before backing out of a proof attempt: test multiple strategies, extract helper lemmas, and keep reusable partial progress.
4. For complex goals, split proofs into helper lemmas with explicit names and purposes.
5. For hard proofs, build helper lemmas and infrastructure instead of forcing brittle one-shot scripts.
6. When infrastructure is broadly useful, move it into reusable helper files/subfolders.
7. Prefer one solid infrastructure pass over many shallow retries on the same terminal goal.
8. Keep unfinished but promising strategies documented in local proof-notes files:
   - module `TODO.md` files (for example in `StringGeometry/RiemannSurfaces/`, `StringGeometry/Supermanifolds/`, `StringGeometry/Topology/`)
   - `ProofIdeas/` notes where available (especially `StringGeometry/Supermanifolds/ProofIdeas/`)
   - relevant `PLAN.md` / status notes near active files
9. Keep module TODO/status tracking updated as obligations move.
10. Re-check nearby definitions whenever a theorem is unexpectedly difficult.
11. Always re-check soundness after progress; successful compilation is necessary but not sufficient.
12. After 2 distinct failed in-file proof attempts, move to scratch/test files, get a compiling micro-lemma, then port back.
13. If backing out of an approach, record the failed route and concrete blocker in local TODO/proof notes.
14. Missing-library policy:
   - when a needed theorem is absent upstream, stop retrying brittle tactics and build the missing local infrastructure lemma/theorem with stable statement shape,
   - keep that infrastructure reusable and documented in local proof notes/TODO.

## Build and tooling rules

1. Do not run bare `lake build`; use targeted builds.
2. Prefer targeted checks such as:
   - `lake env lean StringGeometry/.../<File>.lean`
   - `lake build StringGeometry.<Module.Path>`
3. Never run `lake clean` unless explicitly approved by the user.
4. Use `read_references.py` (repo root) for PDFs in `references/` when reference material is needed.
5. For hard proof work, consult standard references from `references/` early (not only after getting stuck).
6. Keep/update reading notes under `references/` while working:
   - record the exact theorem/section used,
   - map it to the target Lean declaration(s),
   - note any missing bridge lemmas or formalization gaps discovered.
7. Compile frontier rule for each change:
   - build the touched file/module,
   - build the nearest umbrella module importing it,
   - update local TODO/status when frontier or blockers change.
8. Commit gate: only commit when the changed compile frontier builds; include checked modules in the commit message.
9. Lean file size policy:
   - keep `.lean` files under 2000 lines,
   - when a file approaches the limit, split into a subfolder with thematic modules and keep a thin compatibility import at the old path.
10. Before structural/refactor commits, run:
   - `scripts/check_lean_file_length.sh 2000`
   - and include any exceptions/blockers in the local TODO if immediate split is not feasible.

## Practical proof tactics

1. Write proof attempts early and compile frequently to inspect goal states.
2. If a long proof stalls, split it into explicit local/private helper lemmas.
3. When large goals depend on missing abstractions, pause and build the abstraction first.
4. Keep proof scripts explicit when automation is unstable.
5. Keep notes current so proof strategy is recoverable across context-window resets.
6. For Mathlib/API drift breakage, prefer type-stable rewrites (explicit types, robust lemmas, local bridge lemmas) over brittle `simp` chains.
7. After each substantial audit/development pass, update the module `TODO.md` with:
   - current compile snapshot,
   - active blockers,
   - next 3 concrete targets.
