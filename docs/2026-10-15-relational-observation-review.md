# O1 independent finished-implementation review

[AGENT] 2026-10-15. Independently reviewed implementation
`56168ed59da4c8972169bcaee778b767f35c6005` on
`refactor/relational-surface-1013`, against I1 handoff
`b647476a44e5ffd408e1fdf6a6591be71810fefb` and implementation
`5d8e53e9f1a046fb645fce49901de714591e0819`. Customer inputs are immutable
f314a4f7 (RD7) and the later user-relayed 5e8ed98 (RD8), as detailed below.

## Assessment and findings

No new semantic or observer-compatibility defect found. The independently
checked proofs, exact frozen consumers and inspected full validation support
completion of the bounded upstream O1 implementation and exact RD8 O1-A
agreement/prefix/guarded response at the pin above. The O1-R1 completeness
finding is fixed. This does not establish full interface replacement, compiled
renderer correspondence, completion of RD8’s observed caller, live trust
migration, U1 uptake, or authorization to merge/push.

The former inventory circularity (O1-R1) is resolved in this implementation.
`callFrames`/`activeCalls` extract actual function activations independently of
entry/exit site tables. `step_boundary_effect` eliminates every constructor of
the existing `Step`; configuration-producing helpers have separately checked
stack-preservation proofs. Its silent alternative permits unchanged active
frames or the explicit panic-unwind pop, not arbitrary stack changes.
`entry_iff_depth` and `return_iff_depth` connect entry/normal return to the
independent activation-depth changes, with unwinding excluded only for normal
return. The proof is for arbitrary supplied contexts, controls and stores,
without reachability, safety, typing, termination or driver-fuel assumptions.

`entry?_on_transition` and `return?_on_transition` retain exact payload,
pre-store, actual successor and full label. Entry uses the resolved `f.id` but
keeps arguments supplied to `enterFrame`, including captures and unadjusted
receiver inputs. Re-dispatch and delivered entry panic are excluded. Deferred
entries during fall-through, return and panic are covered. Normal exits include
discarded `[]` values regardless of signature, target-result snapshots before
future target evaluation/writeback, and preprint helper returns. Panic frame
unwind and top-level readback are distinct. The machine, drivers and C1/C2
phase/failure semantics have no operational edits.

`History` is the chronological successful-step closure of a generic pre-store
sensitive projection. Erasure, coverage, append, split, uniqueness, arbitrary
residual-tape realization and executable-prefix coverage preserve complete
labels and intermediate states. An unfinished prefix is admitted. No endpoint
success/failure or fabricated error event is added. Empty race labels are not
used as observer-silence evidence; the facade test exhibits an observable pure
return.

## Independently run validation

All runs use `capped`, `LEAN_NUM_THREADS=2`, and reviewer-private temporary and
output directories. Author dependency outputs are read-only inputs, not
independently rebuilt dependencies. No author build output or peer tree was
modified.

- Independently re-elaborated `RelationalObservation`, `RelationalEventFrame`,
  `RelationalEvent`, `RelationalEventSound`, `RelationalHistory`, the
  `GoLean.Relational` facade and `Tests.RelationalObservations` into private
  outputs. All passed. Exact seven-module `leanchecker --verbose` replay passed,
  with one output per requested name and no extra replayed names.
- All twelve headline axiom reports in `Tests.RelationalObservations` use only
  `propext`, `Classical.choice` and `Quot.sound`.
- An independent exhaustive imported-GoLean/local audit passed for 19,671
  declarations (including seven reviewer controls), standard trio only. This
  is an axiom check, not a waiver of opaque/compiled implementation findings.
- Independent facade controls passed for arbitrary preprint result values;
  snapshots with arbitrary future target expressions; silent panic unwind;
  nil deferred invocation without entry; observable ordinary deferred return
  during panic with discarded `[]`; empty events iff neither entry nor normal
  return; and any failed `stepFn` attempt on any tape implies no boundary
  events. The last result follows because each reported boundary has a
  pick-free transition that succeeds on every tape.
- Exact kernel replay passed for the final seven-control reviewer module.

The first isolated build attempt failed because a partial `LEAN_PATH` module
root shadowed missing imports. Read-only dependency links fixed the reviewer
harness; all seven subsequent elaborations passed. Some read-only probes used
incorrect relative working directories and failed visibly; corrected absolute
paths were used for the reported input verification and compatibility build.
These were reviewer harness failures, not production failures.

## Frozen observer and history compatibility

Customer input: `f314a4f7ce69f8e5dc1c835298d4f1a2832a996f`. Independently
verified all 113 experimental package files against immutable git objects.
Only private `lakefile.toml` (new compatibility target) and `pins.json`
(dependency snapshot) differ. All four dependency clones are tracked-clean at
their recorded pins, without root symlinks or git-object alternates. The
private GoLean validation snapshot has exactly the reviewed implementation’s
GoLean source bytes. Reproduction uses the offered implementation pin above;
no disposable snapshot is required.

Independently read and recompiled `O1Compatibility.lean` against the reviewer
O1 outputs and frozen read-only customer imports. `emit_projection` proves
all-state equality with existing `emit`, for arbitrary observers, stores,
controls and tapes; this is stronger than successful-step equality and does
not assume failed attempts execute. `history` proves exact existing
`Safe.Obs` on every successful `Prefix`, including unfinished prefixes.
The proofs preserve designation, supplied arguments, return values and
pre-store inspection. Both report standard axioms only. Exact single-module
`leanchecker --verbose O1Compatibility` replay independently passed. An
independent exhaustive audit checked all 58 declarations defined by this
module, including generated helpers, with standard axioms only.

The original and experimental definitions are not silently substituted:
independently compared exact declaration text for `callEntry?`, `Enters`,
`entered?`, `frameExit?`, `exitValues`, `returnSite?`, `entryEvents`,
`returnEvents`, `emit` and `Silent` at f314a4f7; all agree. Original and
experimental `Observer.lean` and `FrameCont.lean` are byte-identical, and original `Safe.Obs`
from `AbortPrefix.lean` equals the experimental frozen definition exactly.
The original CallSite constructors are retained unchanged in the experimental
file; its other changes remove unneeded downstream proofs. The bridge imports
only `GoLean.Relational` from GoLean and keeps customer records/ownership out
of the public semantics. This f314 bridge alone does not finish RD8 uptake; the later exact frozen
consumers are checked below. No live source-census trust artifact is migrated.

## Exact frozen RD8 request and consumers

The user later relayed logic `5e8ed98ad68c31fa01ad879ed48b9ac8440ddb42` and
the RD8 O1 constraint charter. This review was extended to that immutable
request. The observed caller remains explicitly unfinished downstream;
reviewing its request/guarded consumers does not complete it. U1 is separate.

`RD8Acceptance.events` maps the public `BoundaryEvent` constructors to the
frozen sum `EntryEvent ⊕ ReturnEvent` without changing either payload.
`agreement` has exactly `Observed.EventAgreement events`: arbitrary successful
transitions, contexts/states/labels, observers and tapes. It uses the stronger
all-state O1 equality, not a restricted-state surrogate or a definition of
events from legacy emit. Independent semantic coverage remains the upstream
structural proof reviewed above.

`prefix_history` supplies this agreement to the exact frozen
`prefix_acceptance`; no completion premise is added. `guarded` supplies it to
`observed_step`. Independently compared the entire guarded statement to the
frozen `LiftingTarget` body: byte-for-byte equality after removing only the
filled agreement parameter. Heap validity/update, pick-free step evidence,
nonterminal/admission, heap growth, observer invariant and history ownership
premises all remain. No Iris resources enter upstream semantics.

Independently verified all 125 RD8 frozen package files: only private pins and
lakefile differ. All four clones are clean at exact pins, without root symlinks
or object alternates; the private GoLean sources equal the reviewed lane.
The retained `RD8Acceptance.lean` equals the independently compiled source.
Rebuilt six frozen modules (`ObservationFrozen`, `ObservationRequests`,
`ObservationCompatibility`, `ObservedLifting`, `ObservedAdequacy`,
`ObservationAcceptance`) and both adapters into private outputs, using the
independently rebuilt O1 modules. All passed.

Independently extracted both observed theorem headers from baseline
`97426cab7c87ca52a5e3c480c9cb9b30ac534dde`'s original
`packages/golean-iris/GoLeanIris/Logic/ObservationAdequacy.lean`, and compiled
separate clients applying the closed roots. The frozen acceptance headers
are byte-identical after removing the changed theorem name. SHA-256 of those
remaining header bytes: prefix
`d2ac457e5b00e7e1c60fc4feff72b3fb81eeebd9199837924f8e494b150e7cb9`;
outcomes `0530dbdd2fda6bc5ee1807e31f36878b69ae18006cfc70f6f5794eed9abe4c9b`.
Original StringPlain, argument typing, exit silence, code, and the outcomes'
no-globals/no-initializer/reserved-prefix premises remain unchanged.

An independent audit checked all 184 declarations across those nine rebuilt
modules (six frozen, two adapters, original-header client): standard axioms
only. It also checked direct proof-body edges, not merely statement mentions:
`agreement → O1Compatibility.emit_projection`; `prefix_history → agreement`
and `prefix_acceptance`; `guarded → agreement` and `observed_step`;
`observed_step → GoLean.Logic.History.update`. The audit initially failed
because the review harness had omitted the explicit import of the rebuilt
ObservationCompatibility module; adding that import fixed the harness, and
all asserted module-presence/axiom/dependency checks then passed.
Exact ten-module kernel replay independently passed, with each requested
module replayed once and no missing/extra names.

## Fresh author validation inspected independently

Inspected the author's fresh frozen consumer build logs: RD6 and RD7 each
completed 416 jobs. RD6 retains its 5,940-declaration aggregate and
5,943-declaration acceptance audit; RD7 retains its 6,058-declaration audit,
standard axioms only. These full builds are author evidence, not independent
reviewer rebuilds. The independent O1/bridge builds above have narrower scope.

Independently verified both complete replay-name multisets against actual built
`.olean` inventories: RD6 exactly 407 modules (100 GoLean, 101 local, 206
dependencies), RD7 exactly 411 (100 GoLean, 105 local including O1Compatibility,
206 dependencies), once each. Every local and GoLean source has its output.
The author reports both full replays exited zero. These full replays were not
rerun by the reviewer; their input sets and output completeness were independently
checked. Dependency counts are Iris 174, Batteries 18, Qq 14.

Also independently verified all 106 RD6 frozen files at bbb372e2: only private
lakefile.toml and pins.json differ. Its four clones are clean at the prescribed
pins, with no root symlinks/alternates; its GoLean sources match the reviewed O1
lane. The three original C2 clients remain present; `OriginalAcceptance` still
explicitly takes `assembly : InitAssembly`. Frozen RD7 inputs and clone checks
are described above. No original consumer Lean source was edited.

Inspected D1's fresh build/audit and preservation logs: standard-axiom audit
passes; implementation scan explicitly **FAILS with 16 findings**, unwaived;
the archived-C1 comparator/shadow/detector control matches byte-for-byte.
D1 replay contains exactly its eight Concurrency modules plus five
relational/audit clients, including the new observations test. The fresh upstream `scripts/ci --diff` log records **PASS**, 2,115 seconds:
235 warning-free build jobs, exact replay of 100 GoLean modules, exhaustive
core audit, 396 eval tests, all frontend/boundary/scheduler checks, and all
speedbumps green. Fresh differential: 4,025 cases, 3,767 PASS and 258 tracked
FAIL; fresh negative: 415 PASS. Full baseline comparisons report no
regression/cause drift, and baselines are unchanged. The raw differential
runner exits 1 for that tracked failing set; the baseline-comparison gate
passes. This is inspected author evidence, not an independent full CI rerun.
The log explicitly certifies the dirty tested worktree, not an exact commit
invocation; the source-freeze binding is separate.

The author’s full frozen RD8 build passes 431 jobs and its existing aggregate
audit checks 6,407 local declarations with standard axioms. Independently
matched its completed full replay-name multiset: exactly 423 modules
(100 GoLean, 117 local including both adapters, 206 dependencies), once each.
All 217 local/upstream source outputs exist. The author reports exit zero.
This full replay is inspected author evidence; the separate ten-module
reviewer replay above was run independently.

## Immutable source binding

Independently matched all 4,353 recorded checked code/configuration/script/corpus
SHA-256 values to committed blobs at
`56168ed59da4c8972169bcaee778b767f35c6005`. Independently matched all seven
reviewer-rebuilt O1 source modules and both retained compatibility/RD8 adapters
to that commit. The remaining Lean change is exactly the single new-test import
in Tests/GoCoreAudit; the Lake target addition and documentation were inspected.
All 100 GoLean `.olean` files in each RD6/RD7/RD8 private package are
byte-identical to the root gate outputs, independently compared. The tested
and replayed implementation is therefore concretely bound to this pin; the
original dirty-tree CI invocation remains described honestly.

## Trust limits and remaining obligations

The 16 inherited implementation findings remain open and unwaived. In
particular, semantic proofs and old/new observer projection equality use the
same kernel-visible machine operations; they do not prove that compiled
opaque Ty/GoValue/Expr renderers compute those semantic constants.
`preprintDispatch`, `unseqAtom` and `valueEq` are known load-bearing paths.
Payload/timing coverage does not settle exact executed diagnostic/printing
text correspondence. The stage now states the bounded follow-up precisely: for each reachable
Ty/GoValue/Expr generated printer, every finite input, precedence and caller
formatting width/indent, the pinned implementation must terminate with the
formatted output of a total kernel-visible specification; nested/mutual
dependencies and composition preserving complete Stop payloads are included.
It explicitly does not claim unsupported equality to old opaque constants.
That wording preserves the successful-step theorem scope and correctly blocks
executed-renderer/full-landing claims. No documentation defect found.

Independently reran the recorded dependency probe against reviewer O1 outputs;
all ten root results match. Entry/return projections and preprintDispatch reach
the value renderer; unseqAtom also reaches Expr; valueEq also reaches Ty; the
three drivers reach all three. Config.abort? and raceUpdate reach none through
this probe. The probe stops at opaque endpoints, so these empty results do
not establish absence of hidden compiled dependencies.

The inherited `Memory.lean:1625` unused-h warning and recorded live
**35 NOT-PUBLIC** failure remain open. Neither is borrowed as fresh evidence;
this review did not rerun the live customer gate. No concurrent/infinite-run
adequacy, all-schedule safety, U1/O1 combined uptake, renderer waiver, main
merge, push or live repin follows from this report.

## Reproduction

Snapshot the seven source modules above into a private source root. Compile
in that order with `lake env lean --root=<source-root> -o
<private-lib>/<module>.olean <source>`, prepending the private lib inside
`lake env`; fill otherwise-missing module imports with read-only links to the
completed author build. Replay exactly those seven module names. The review
controls and exhaustive axiom scan are reproduced in the source appendix below;
save it as `O1Review.lean`, compile it into the private root and replay
`O1Review`.
For compatibility, reproduce the frozen f314a4f7 experimental package and
its dependency pins, add the separately preserved O1 compatibility source,
then compile/replay it with reviewer O1 outputs first in `LEAN_PATH`.
Use `capped`, two Lean threads and a private `TMPDIR` for all commands.

## Independent facade control and axiom-audit source

```lean
import GoLean.Relational
import Lean

open GoLean GoCore Relational Boundary Machine
namespace O1Review

-- A normal exit snapshots even an arbitrary preprint result before its later
-- string-only delivery can fail. No result typing premise is imposed.
theorem arbitrary_preprint_exit {ctx s rl older entry newer k env fid v tr}
    (hl : Mem.loadBinding ctx s rl = .ok (v, tr)) :
    events ctx ⟨.signal .ret (.frame [] env [rl] [] (.preprintK older entry newer k) fid), s⟩ =
      [.returned ⟨fid, [v], s⟩] := by
  apply events_return_iff.mpr
  apply return?_iff.mpr
  exact ⟨_, _, Returns.intro (mode := .explicit) (ExitSite.preprint hl)⟩

-- Snapshot is independent of the target expression's future success.
theorem arbitrary_target_exit {ctx s sh e ops rest roots k env fid vs tr}
    (hl : loadResults ctx s roots = .ok (vs, tr)) :
    events ctx ⟨.next (.frame ((sh, e :: ops) :: rest) env roots [] k fid), s⟩ =
      [.returned ⟨fid, vs, s⟩] := by
  apply events_return_iff.mpr
  apply return?_iff.mpr
  exact ⟨_, _, Returns.intro (mode := .falling) (ExitSite.targets hl)⟩

-- Panic propagation popping a function is explicitly not normal return.
theorem unwind_not_return (ctx s chain plans env roots k fid) :
    events ctx ⟨.panicking chain (.frame plans env roots [] k fid), s⟩ = [] := rfl

-- An invocation of a nil deferred value panics without entering a body.
theorem nil_defer_not_entry (ctx s plans env roots ds k fid args) :
    events ctx ⟨.next (.frame plans env roots ((.nil, args) :: ds) k fid), s⟩ = [] := rfl

-- A deferred frame's ordinary normal return remains observable even with a
-- panic-resumption continuation below it; its result payload stays empty.
theorem deferred_return_during_panic (ctx s chain k fid) :
    events ctx ⟨.next (.frame [] [] [] [] (.panicResumeK chain k) fid), s⟩ =
      [.returned ⟨fid, [], s⟩] := rfl

-- Generic completeness of the empty-event case follows without reachability.
theorem empty_iff_no_boundary {ctx a b l} (h : Transition ctx a l b) :
    events ctx a = [] ↔ (¬ ∃ e, Enters ctx a b l e) ∧ (¬ ∃ e, Returns ctx a b l e) := by
  constructor
  · intro hn
    constructor
    · rintro ⟨e, he⟩
      have hx := events_entry_iff.mpr ((entry?_on_transition h).mpr he)
      simp [hn] at hx
    · rintro ⟨e, he⟩
      have hx := events_return_iff.mpr ((return?_on_transition h).mpr he)
      simp [hn] at hx
  · rintro ⟨he, hr⟩
    rcases h.boundary_cases with ⟨hn, _⟩ | ⟨e, _, hx, _⟩ | ⟨e, _, hx, _⟩
    · exact hn
    · exact (he ⟨e, hx⟩).elim
    · exact (hr ⟨e, hx⟩).elim

-- A failure on any supplied tape cannot have a semantic entry/return,
-- since both boundary operations are pick-free and succeed on every tape.
theorem failed_attempt_has_no_events {ctx a ch stop}
    (hf : stepFn ctx a.store a.control ch = .error stop) : events ctx a = [] := by
  rcases events_cases ctx a with hn | ⟨e, he⟩ | ⟨e, he⟩
  · exact hn
  · obtain ⟨b, l, entry⟩ := entry?_iff.mp (events_entry_iff.mp he)
    have hp : l.picks = [] := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := entry
      rfl
    have hs := entry.transition.on_any_tape hp ch
    rw [hf] at hs
    cases hs
  · obtain ⟨b, l, ret⟩ := return?_iff.mp (events_return_iff.mp he)
    have hp : l.picks = [] := by cases ret; rfl
    have hs := ret.transition.on_any_tape hp ch
    rw [hf] at hs
    cases hs

end O1Review
open Lean in
run_elab do
  let env ← getEnv
  let mut checked := 0
  for (n, _) in env.constants.toList do
    let ours := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!.getRoot == `GoLean
      | none => true
    unless ours do continue
    for ax in (← collectAxioms n) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Forbidden axiom: {n}: {ax}"
    checked := checked + 1
  logInfo s!"O1 independent axiom audit: {checked} imported GoLean and local declarations; standard trio only"
```

For the frozen-client helper audit, save the following as
`O1CompatibilityAudit.lean` and compile in the frozen package with private O1
outputs first in `LEAN_PATH`. It rejects an empty module or any non-standard
axiom; the observed count was 58.

```lean
import O1Compatibility
import Lean
open Lean in
run_elab do
  let env ← getEnv
  let mut checked := 0
  for (n, _) in env.constants.toList do
    let ours := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]! == `O1Compatibility
      | none => false
    unless ours do continue
    for ax in (← collectAxioms n) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Forbidden axiom: {n}: {ax}"
    checked := checked + 1
  if checked == 0 then throwError "Empty compatibility audit"
  logInfo s!"O1 compatibility exhaustive axiom audit: {checked} declarations; standard trio only"
```

For the exact RD8 replay, rebuild the six frozen modules listed above, then
O1Compatibility, RD8Acceptance and the original-header client into a private
root. The two headers are recovered directly from original baseline
ObservationAdequacy.lean; their proof applications are the identical
applications retained in frozen ObservationAcceptance.lean. Save the following
as RD8ReviewAudit.lean and include it in the exact ten-module replay.

```lean
import RelationalCodeX.ObservationCompatibility
import RD8Acceptance
import RD8OriginalHeaders
import Lean
open Lean
run_elab do
  let env ← getEnv
  let names := [`RelationalCodeX.ObservationFrozen, `RelationalCodeX.ObservationRequests,
    `RelationalCodeX.ObservationCompatibility, `RelationalCodeX.ObservedLifting,
    `RelationalCodeX.ObservedAdequacy, `RelationalCodeX.ObservationAcceptance,
    `O1Compatibility, `RD8Acceptance, `RD8OriginalHeaders]
  for name in names do
    unless env.header.moduleNames.contains name do throwError "Missing module {name}"
  let mut checked := 0
  for (n, _) in env.constants.toList do
    let ours := match env.getModuleIdxFor? n with
      | some i => names.contains env.header.moduleNames[i.toNat]!
      | none => false
    unless ours do continue
    for ax in (← collectAxioms n) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Forbidden axiom: {n}: {ax}"
    checked := checked + 1
  logInfo s!"RD8 review axiom audit: {checked} declarations in nine rebuilt modules; standard trio only"
  for (root, targets) in [
    (`RD8Acceptance.agreement, [`O1Compatibility.emit_projection]),
    (`RD8Acceptance.prefix_history, [`RD8Acceptance.agreement, `RelationalCodeX.Observed.prefix_acceptance]),
    (`RD8Acceptance.guarded, [`RD8Acceptance.agreement, `RelationalCodeX.Observed.observed_step]),
    (`RelationalCodeX.Observed.observed_step, [`GoLean.Logic.History.update])] do
    let some info := env.find? root | throwError "Missing {root}"
    let some value := info.value? (allowOpaque := true) | throwError "No body for {root}"
    for target in targets do
      unless value.getUsedConstants.contains target do
        throwError "Missing direct proof-body edge {root} to {target}"
      logInfo m!"Proof-body edge: {root} -> {target}"
```
