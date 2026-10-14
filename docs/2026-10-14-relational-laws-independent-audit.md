# Independent relational-law audit — 2026-10-14

## Target and judgement

[AGENT] 2026-10-14: independently reviewed commit
`b25a47ef60984e2da16f80dedc0a1d5945806b8f`, starting with its delta from
`ee1392b4`. **No new correctness, trust or acceptance defect found in this
law batch.** This is an audit judgement, not merge/push authorization or a
claim that the broader relational interface or downstream Iris proof is complete.

The reviewer used branch `audit/relational-laws-1014`, worktree
`/home/mike/projects/golean/.claude/worktrees/relational-laws-audit-1014`,
at the exact target. Neither team's source worktree was edited. The build
cache was copied with `cp -a --reflink=auto` into this reviewer worktree;
no shared symlink or hardlink cache was used. Lake checked the target's
source/build dependencies; this was a warm-cache review, not a cold rebuild.
Every Lean/Lake job used `LEAN_NUM_THREADS=2` and `capped`.

The review followed the new proofs into the semantic relation, memory
operations, sequence continuation construction, finite-run correspondence,
pick-free uniqueness/progress and the full eight-module downstream acceptance
closure. Previous reviews were not treated as settled conclusions.

## Findings and conclusions

There are no new findings requiring a fix or waiver. The following are
checked conclusions and explicit limits, not hidden dispositions:

1. **Exact requested types and domains.** The three assignments
   `rq1 : Requests.ReadVariableLaw := read_variable`,
   `rq2 : Requests.SequenceSpliceLaw := sequence_splice` and
   `rq3 : Requests.AssignPointerVariablesLaw := assign_pointer_variables`
   elaborate unchanged. No wrapper adds `MachineWf`, typing, refusal-freedom,
   root-target or distinct-location assumptions. `loadRoot` still restricts
   successful *binding-slot* reads to roots; that pre-existing operation
   domain is present in the requests themselves. The assignment target
   remains arbitrary `Loc` and is constrained only by the successful write.
2. **Actual labels.** `read_variable` uses `Mem.loadBindingFor` and the actual
   continuation's `projChainTarget`, retaining a potentially projected read
   footprint. It does not claim a silent trace. Assignment reads both operands
   before its write, emits the canonical target write label through the
   existing `storeTarget`/`Mem.store` path, and retains all administrative
   transitions in its ordered `Run`. Its existential trace lists hide their
   concrete shape, not their relationship to actual transitions. Empty picks
   and output hold at each step; memory-access traces are not erased.
3. **Aliasing, interior targets and cleanup.** The assignment proof performs
   both reads in `s`, then applies precisely `storeLoc ctx s target value =
   .ok t`; it never rereads an overwritten operand. The reviewer independently
   instantiated the law with a genuine interior array update and with all
   three locations and both identifiers equal (source below). The latter is
   a witness of the deliberately operation-based domain, not a claim of
   Go source typing. `empty_sequence_run` correctly distinguishes a same-env
   governing sequence (one step, empty splice) from every other continuation
   (wrap then remove the empty sequence, two steps). Its endpoint is exactly
   `resumed k t`; it does not execute the caller's remaining statements.
   `sequence_splice` itself requires the same environment on both sides.
4. **Acceptance premises and refusal-sensitive safety.** The unchanged
   acceptance derives its parameter reads from the two fresh slots, derives
   its root write from `write_read_root` and Boolean normalization, preserves
   the two pre-existing roots across allocation, and derives the framed-root
   result using `b.id ≠ a.id`. Neither operational law is an unproved parameter
   of the checked `set_root` wrapper. `Segment.normal_progress` chains
   pick-free successors to halt. The crucial dependency is
   `Transition.on_any_tape`/`unique_of_no_picks`: a pick-free successful step
   works on every tape and fixes every successful successor. Together with
   the halt elimination theorem, this supports progress at *every reachable*
   point, not just along one lucky execution. `PickFreeProgress.run` then
   excludes stopping errors on every tape, allowing fuel exhaustion. This
   is the deterministic fragment; no general choiceful safety claim follows.
5. **Exports, trust and behavior.** `GoLean.Relational` imports the new module;
   the on-disk core audit includes it and the contract module prints the three
   headline axioms. The delta adds theorem/proof code and imports, tests and
   documentation; it changes no evaluator, Step relation, memory operation,
   frontend or differential baseline. Inspection found no new trust escape.
   The broader source scan's apparent `unsafe`/`sorry`/`implemented_by` hits
   were comments or Go value/type names, not Lean escapes. Kernel replay and
   the core axiom audit passed as detailed below.
6. **Remaining scope.** This acceptance is a local semantic prerequisite,
   not an Iris ownership proof, an interior separation/frame theorem, callable
   lookup/dispatch integration, concurrency sequentialization, general
   outcome/refusal coverage, or complete observation coverage. Those remain
   open as documented. The public law statements now avoid target/RHS/store
   continuation bookkeeping for these three constructs; the downstream
   closure still contains the explicitly acknowledged driver-frame boundary
   and allocation representation coupling. This does not establish construct
   usability for the whole language.

## Frozen downstream inputs

Copied byte-for-byte from
`/home/mike/projects/golean-logic/.claude/worktrees/relational-demo/experiments/2026-10-14_relational-demo/RelationalDemo/`
into the reviewer's `.tmp/acceptance/RelationalDemo/` before building. The
original `Requests` and `Acceptance` hashes match the target handoff exactly.
The remaining six hashes identify the complete frozen closure independently:

```text
Acceptance: 84a3222fac13ce257eba52753a1a4b9e258ea54fd4239880cf4546c9de55e485
Activation: d3c27ad2ff4588cbbcc6d8a86ac169726cd80906909cbdb6b9b2cafc393e4c79
Boundary: dd7d7c227a0b50ade49e37868824e8ab4355ca3f1a491da5e93bb334de312a23
Control: f0f2d5933b777c9389332178be8b7c0824e884c496663dd42280486954d2fa25
Fixture: 3f4ec8dd92afa9934b7c8902c97b28736d3a8a12c39cb1fd42fc41d7a9f55c84
Memory: fac0cf9e80ce7b125cd34217d981052610b628ce735d00c33153e41f9e9a97f8
Requests: 094044792f9fddaf10286193697c2c424d7e707ee65277890a85a0473ed41a05
Segments: e7b2f9c392fb8783f79f7d1ba852f3990c12627706fcd8d2980c769618bee977
```

The aggregate `RelationalDemo.lean` and Iris modules were not imported.
The unchanged eight modules were supplemented only by `AcceptanceCheck.lean`,
containing the two Lean snippets printed verbatim in the target's
`docs/2026-10-14_relational-demo-laws.md`. Thus it includes the exact three
law assignments and the fully written `read_parameters` and `set_root`
conclusions, not inferred or weakened substitute statements.

## Reproduced validation and evidence scope

From the isolated acceptance package, using the target handoff's Lake recipe
and `lean-toolchain` (adjust only the GoLean local path):

```sh
LEAN_NUM_THREADS=2 capped lake build
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose GoLean RelationalDemo AcceptanceCheck
```

Both exited 0. The acceptance build completed 55 jobs. `#print axioms` for
`rq1`, `rq2`, `rq3`, `read_parameters` and `set_root` reported exactly
`propext`, `Classical.choice`, `Quot.sound`.

Replay emitted exactly **89 unique module names**, equal to the source set:
all 79 `GoLean/**/*.lean` modules plus root `GoLean.lean`, the eight frozen
`RelationalDemo` sources and `AcceptanceCheck.lean`. Missing, stale and
repeated modules: zero. The comparison constructed names from these source
paths and compared them to the `replaying ...` lines, rather than relying
on a module count alone. There were no other replay log lines. This is fresh
kernel replay of the built modules, not merely a green Lake build.

From the reviewer GoLean root:

```sh
LEAN_NUM_THREADS=2 capped lake build GoCoreAuditTests
LEAN_NUM_THREADS=2 capped scripts/check-core-audit
```

Both exited 0. Core audit: 79 non-root GoLean modules (68 under GoCore),
348 required theorems present, 22,160 declarations across imported local
modules, classical trio only. The three new headline axioms also printed
successfully through `Tests.RelationalContracts`.

**Full CI was not independently rerun in this audit.** The target handoff
reports a 742-second `scripts/ci --diff` run, 3,989 fresh differential rows
(3,749 PASS, 240 classified known FAIL), 405 negative rows and all speedbumps
green, at the pre-commit dirty tree with only documentation finalized later.
Its ephemeral `.tmp` had already been removed when reviewed; I could not
independently authenticate that run's metadata against the final committed
source. Treat it as documented historical evidence, not this review's
clean-commit full CI result. The new delta contains no executable behavior
changes, so the targeted acceptance/trust checks were appropriate audit
reproduction. The charter's applicable fresh full-CI/merge requirements
remain separate and are not waived by this report.

## Reviewer-only supplemental checks

These two non-vacuity checks are separate from the unchanged downstream
acceptance. To reproduce, write the following to a local scratch
`Supplemental.lean` and run, from the target GoLean root:

```sh
LEAN_NUM_THREADS=2 capped lake env lean /absolute/path/to/Supplemental.lean
```

The reviewer ran that command successfully; both theorem axiom lists were
the standard trio. Every lookup/read/write premise reduces directly, and
`k` stays symbolic. These source checks were elaborated by Lean's kernel;
they were not added to the 89-module replay set or the permanent test suite.

```lean
import GoLean.Relational
open GoLean GoLean.GoCore GoLean.GoCore.Relational
namespace IndependentAudit
def ctx : ProgramCtx := ProgramCtx.ofTables (types := #[])
def zero : Loc := .base ⟨0⟩
def selfStore : Store := {heap := #[.value (.pointer .bool) (.addr zero)]}
def selfEnv : LocalEnv := LocalEnv.declare [] 0 zero
-- All three locations and both identifiers coincide. No premise is assumed.
theorem self_alias (k : Continuation) :
    ∃ ls, Run ctx (statement (.assign (.addr (.var 0)) (.var 0)) selfEnv k selfStore)
      ls (resumed k selfStore) ∧ (∀ l ∈ ls, l.picks = []) ∧ (∀ l ∈ ls, l.out = []) :=
  assign_pointer_variables ctx selfStore selfStore selfEnv k 0 0 zero zero zero
    (.addr zero) rfl rfl (by rfl) (by rfl) (by rfl)
def leaf : Loc := .index zero 1
def interiorStore (b : Bool) : Store := {heap := #[
  .value (.array 2 .bool) (.array #[.bool false, .bool b]),
  .value (.pointer .bool) (.addr leaf), .value .bool (.bool true)]}
def interiorEnv : LocalEnv := (LocalEnv.declare [] 0 (.base ⟨1⟩)).declare 1 (.base ⟨2⟩)
-- A genuinely interior write changes the endpoint; both operation reads and write reduce.
theorem interior (k : Continuation) :
    ∃ ls, Run ctx (statement (.assign (.addr (.var 0)) (.var 1)) interiorEnv k (interiorStore false))
      ls (resumed k (interiorStore true)) ∧ (∀ l ∈ ls, l.picks = []) ∧ (∀ l ∈ ls, l.out = []) :=
  assign_pointer_variables ctx (interiorStore false) (interiorStore true) interiorEnv k 0 1
    (.base ⟨1⟩) (.base ⟨2⟩) leaf (.bool true) rfl rfl (by rfl) (by rfl) (by rfl)
#print axioms self_alias
#print axioms interior
end IndependentAudit
```

No raw logs or copied caches are part of this report. The reviewer scratch
is disposable after the coordinating agent preserves this conclusion.
