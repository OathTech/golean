# Independent recovery control review

[AGENT] root integrator, 2026-09-06. **Bounded PASS** for the twenty-one
frozen inputs in `sources.sha256`, based on independently reviewed entry
`63769964`. This accepts the structural control, preservation/progress and
successful-run increment. The complete O2 outcome remains unfinished.

I read all fifteen new semantic modules, both test/audit modules, the gate
and poison runner, and the contract ledger. Admission is the previously
independent source judgment. No `Control`, continuation or `Inv` constructor
contains evaluation success, future safety, artifact identity or a desired
WP. `Advances` is proved from these structural facts. Its quantifier ranges
over every incoming choice stream, with exactly the original residual
stream. Applying interpreter completeness to an arbitrary relational step
then establishes all-successor preservation; this does not choose a
convenient relational successor.

The current computation and continuation are both typed. Pending arguments
and evaluated values retain their ordered signatures; captures retain live
Boolean roots. Declarations jointly type the current and saved sequence
environments. Block exit restores the saved context; compatible context
union is used only for neutral sequence splicing. Ordinary and deferred
entry reuse the reviewed actual binder/allocator/pinning path. Result
writeback requires a real caller continuation when plans are nonempty.
This condition repairs the draft's synthetic writeback-to-stop/resume case
without excluding actual entry, ordinary calls or deferred calls.

Panic chains admit arbitrary bytes and repeated equal payloads. Actual
recover traversal preserves continuation typing, distinguishes direct and
indirect calls, and retains the newest-entry rule. Normal exit and panic
unwind invoke the same typed deferred entry. The proof does not assume
exclusive ownership of a captured cell, or grant Iris ownership from its
semantic liveness.

## Fresh independent evidence

`compile.py` recreates all seventeen exact frozen semantic/test/audit
modules in a separate source overlay and elaborates them in dependency
order. Its older dependencies are copied from the reviewer's own
`typed-recovery-setup` build at `63769964`; no compiled control module is
borrowed from the author. `source-2.log` completed with exit 0.
`sources.tar.gz` preserves every frozen input. `base-sources.sha256`
records the reviewer's semantic/test source and pins. The reviewer also ran the
default capped `lake build` (`build.log`).

To reproduce, use a separate checkout of `63769964` and this evidence
directory. Verify `base-sources.sha256` against that checkout. Build its
`RecoverySetupTests` target with the stated cap, then copy its compiled
`GoLean` and `Tests` package directories into a unique scratch directory.
Extract `sources.tar.gz` there and copy `compile.py` and `modules.json`
beside the extracted source. From the base checkout, run
`GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped lake env python3
<scratch>/compile.py`. Finally run capped `lake env env
LEAN_PATH=<scratch> lean <evidence>/Probes.lean`. The scratch contains all
package imports, and its new control objects were compiled from the frozen
source. No author build directory is required.

Fourteen additional kernel probes in `Probes.lean` completed with exit 0:

- Missing deferred targets, a changed closure identity, nil captures,
  incorrect value kind and missing arguments cannot satisfy the contract.
- Result roots and writeback references may alias. A separately constructed
  admitted two-result call writes twice to one result cell; the actual
  driver returns the last value, false.
- Equal recovered/repanic history retains arbitrary bytes. An integer
  cannot inhabit the typed chain. Actual unwind appends suspended history
  before the new chain and retains arbitrary original choices.
- A second direct recovery returns nil.
- `Control` plus the actual `Config.abort?` query proves that the first
  payload is a boxed string. This conclusion uses the chain invariant,
  never a guess from the eventual rendered message.

`probes-2.log` records the existing 124-export audit and an independent
complete imported/local sweep of 13,855 declarations, allowing only the
classical foundational trio. The author's dedicated gate additionally
freshly elaborated all seventeen modules and rejected all seventeen
compiled poisons (`author-gate-2.log`). These are evidence for the frozen
control scope, not final runtime or Iris conformance.

## Findings and limits

The first author audit inventory mistook the prose word `goal` for a
theorem name. The gate failed, and the author removed only that nonexistent
export before its successful second run. All semantic/test source hashes
remained unchanged. The first reviewer overlay failed because Lean resolves
an entire package under the first package root; copying the reviewer's
existing dependencies into that overlay fixed its construction. The first
reviewer probe run had an unconstrained entry metavariable in the integer
rejection proof; spelling out the entry fixed it. All three failed logs
are retained and are not counted as successful validation.

`Inv.readout` proves value shape and arity. Successful driver hypotheses in
`run_readout` and `run_choices` are explicitly partial-correctness contracts.
Progress treats a nonempty top-level panic chain as semantic abort; the
current renderer can still refuse invalid UTF-8/equal-repanic observations.
This review does not waive actual driver terminal/fuel/no-refusal contracts,
rendering repair, reusable Iris call/unwind rules, or both required customer
proofs. The arbitrary-byte and repeated-panic profile must remain intact.

Author ordinary CI, integrated public-interface checks, native/spike gates,
and the eventual B7 migration remain separate integration prerequisites.
This report makes no claim about a still-running CI process or a completed
O2, O4 or sprint.
