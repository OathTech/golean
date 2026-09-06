# Boolean static admission validation, 2026-09-06

Bounded static O1 increment on `typed-boolean`, starting from `10fefeb3`.
The implementation tree is bound by `sources.sha256`; this evidence was
produced before the commit, so command metadata correctly records that
starting HEAD and a dirty worktree. Main was not changed.

## Fresh evidence

- `focused.log`: complete `scripts/check-boolean-typing` PASS. Library and
  source elaboration, all 38 kernel regression/family/fixture theorems,
  post-import audit (12 required theorem exports, 3276 local constants),
  three compiled-then-rejected poison controls, complete fresh native
  artifact comparison, and 3/3 focused Go-versus-Lean cases.
- `focused.tsv` / `focused.meta.tsv`: the exact focused differential
  result/metadata. Choice-invariance checks report no wide choice sites.
- `native.json`: fresh whole wire artifact used by the focused harness;
  the whole lowered program is checked against `BooleanTypingFixture`.
- `shadow.stdout`: actual Go observation for the initializer-scope
  discriminator, Boolean false. An initializer reading the new zeroed
  cell instead of the outer binding would produce true.
- `ci.log`: ordinary capped `scripts/ci` PASS, including both existing
  admission/interface audits, the new typing gate, warning-free core
  `lake build`, frontend pins/unit tests and 202/202 interpreter eval tests.

All Lean/Lake commands used `scripts/capped` with `GOLEAN_MEM_MAX=16G`
and `LEAN_NUM_THREADS=3`. The Go oracle was the existing `go1.26.5` pin.

## Explicitly cached evidence

Ordinary CI compared the previously sealed full executable/negative
records from `docs/evidence/2026-09-05_bug103-integration`, recorded at
`8d8f5487`. Their SHA256SUMS were verified before copying them into this
worktree's cached-report locations. They contain 3598 executable cases and
394 Go-oracle negative cases, with no baseline drift. CI explicitly labels
both records stale relative to the lane HEAD. This is not a fresh full
conformance run for this increment or GoLean frontend-negative evidence.
The lane changes no existing interpreter/frontend execution semantics.

The fresh sprint-wide baseline is a separate parent/preflight deliverable.
The two existing report-only reconciliation findings (C13, C5) remain.

## Independent review

The `typed_contract_review` agent reviewed the static source and evidence
independently. Its two substantive requests were implemented:

1. Sequence declarations must flow into the surrounding sequence because
   `seqCont` splices same-environment lists. Added context effects and
   positive/negative regressions for visibility and duplicate declarations.
2. Native shadowing must challenge initializer scope. Replaced the weak
   constant initializer with outer `x := true`, inner `x := !x`, and a
   result that distinguishes outer lookup from premature inner declaration.

It also required the standalone new gate to audit its own complete imported
local closure and unused/trailing declarations; the audit and all three
compiled poison controls are included in the final passing gate.

Final disposition: **PASS for the bounded static increment**, with no
remaining blocking static finding. The reviewer inspected the final
executable evidence rather than independently rerunning that gate. Ordinary
CI subsequently completed with exit 0 before commit.

This is not acceptance of full O1 or O3: generic driver setup, runtime
invariants, preservation, progress, typed readout, public-interface
integration and the expanded integrated review remain required sprint work.
No stable-interface, full-Go typing, or refusal-freedom claim is made here.
