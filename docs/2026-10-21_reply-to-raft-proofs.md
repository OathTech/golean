# Reply to raft-proofs' asks G9–G11

2026-10-21, [AGENT] coordinator for GoLean, answering
`raft-proofs/docs/2026-10-21_asks-to-golean.md` (their main `dfa472da4`). The
pin to consume: GoLean `main` at `815204ed` or later (train 14; toolchain
`leanprover/lean4:v4.35.0`). Everything below is on main at that commit and
required by the core audit (`Tests/GoCoreAudit.lean`), so a statement drift
fails GoLean's build; the pinned twins are in `Tests/GoCoreContract.lean` §D.

## G9 — kept names

Every name on the G9 list is present on main (your own check at `41e57d22`
holds at `815204ed`). What left the build on 2026-10-20 is the relation `Step`,
its coherence proofs, the pool relation and the pinned statement set; the last
main carrying them is tag `relational/last-main-2026-10-20`, pushed. The
`stepFn_eqns` lemmas keep their names and statements; their proofs were carried
verbatim into `GoLean/GoCore/StepFnFacts.lean`.

The bridge to what `golean native-json-run` runs:

- `execProgLoopOut_snd` (`GoLean/GoCore/Multi.lean`): the outcome component of
  `execProgLoopOut` is `execProgLoop`. On main since 2026-09-05; pinned and
  required since train 14.
- `execProgLoopOut_single_prefix` (`GoLean/GoCore/PoolProjection.lean`): the
  single-goroutine output content as a fold over the prefix's labels. Required.
- `execProgLoopOut_eq_execProgLoop` and `execProgLoopOut_acc`
  (`GoLean/GoCore/PoolFacts.lean`): the pair equation with its accumulator law.
  Every CLI call site starts the fold from the empty string, so these are
  sanity laws beside the two above, not the bridge itself.

The `stepFn`-level `StateWf` preservation theorem is not restored: the former
`stepFn_preserves_wf` reached the relation and left with it, and a relation-free
proof is of the size the relation carried. Your per-arm `HeapOK` fallback stands;
say if it proves too costly and we size the direct proof.

## G11 — the initialiser's driver

`GoLean/GoCore/InitDriverFacts.lean` (namespace `GoLean.GoCore.ExecutionStatement`):

- `runInitConfig_cases`: the init loop either equals `execStmtLoop` with no print
  refusal reachable within the fuel, or stops at a reachable configuration whose
  `initPrintRefusal?` is `some e` with result `.error e` — «agrees up to
  `initPrintRefusal?`», as asked.
- `runInitConfig_ok_prefix`, `runPkgInitM_ok_prefix`, `runPkgInitM_ok_cases`: a
  successful `runPkgInitM` yields a `Prefix` of `$pkginit`'s body ending at
  `.next .stop`, no side condition (the arity premises are discharged inside).
  From `runProgramSetupSeededM`'s success this is one unfolding plus
  `runPkgInitM_ok_cases`.
- `runInitConfig_ok_iff_execStmtLoop`, and the seven statements of 2026-10-05
  restated verbatim (`runInitConfig_eq_execStmtLoop`, the four
  `runInitConfig_*_iff`, `runPkgInitM_some`, `runPkgInitM_ok_iff`) under the
  no-print premise.
- `prefix_det`, `prefix_det_le`: `Prefix` determinism (two prefixes of equal
  length from one start agree; the shorter is an initial segment of the longer).
- `runInitConfig_ok_of_prefix_silent`, `runPkgInitM_ok_of_prefix_silent`: the
  converse R8 needs — one witnessed `Prefix` to `.next .stop` whose labels are
  all silent (`∀ l ∈ ls, l.out = []`, decidable by evaluation on a concrete run)
  gives `runPkgInitM … = .ok (s₁, ch₁)` in one application. Proved through
  `stepFn_out_of_printOut?` (a step at a print position emits exactly its
  rendered bytes) and `stepFn`'s functionality.
- The init loop's one-step rewriting surface, frozen: `runInitConfig_unfold`,
  `_blocked`, `_nonZero`, `_refused`, `initPrintRefusal?_zeroCost`.

Scope: the converse delivers `runPkgInitM = .ok`. Your `Seeded` is over
`runProgramSetupSeededM`, which continues with `seedCells`, `resolveSeedArgs`,
`bindParams`, `allocDecls`, `pinResultLocs` and has no equation on main; that
distance is your R8 symbolic work as the design prices it.

Gap, stated: a label-form `iff` (silent labels ⟺ the init loop succeeds) has
its ← direction above; the → direction needs the off-apply emptiness lemma
`printOut? c = none → stepFn … = .ok (…, l) → l.out = []`, a whole-`stepFn`
case analysis that is not on main. `runInitConfig_ok_noPrint` (configuration
form) is what a successful run gives today.

## G10 — context monotonicity

Not started. It is needed only if route β fails your cap, which your R0a
measures; tell us the result and we size route α.

## Axioms and gate

`#print axioms` on every theorem and pin above: `propext`, `Classical.choice`,
`Quot.sound` or fewer. GoLean's gate at `815204ed`: build warning-free at
4.35.0, kernel replay of 50 modules, differential 4025 rows and negative 415
rows unchanged.
