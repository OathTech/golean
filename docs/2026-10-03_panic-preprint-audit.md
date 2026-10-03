# Pre-merge adversarial audit — lane `core/panic-preprint-1003` (window unit 6b, BUG-004 item 4: the preprint phase)

[AGENT auditor], 2026-10-03, branch `review/panic-preprint-1003` (worktree `.claude/worktrees/audit-panic-preprint`,
fresh `.lake`, `deps/` at the pins via `scripts/setup-deps --from`). Candidate tip `517f9883` (one commit over `main` @
`aeab81c5`); main's binary built from `git archive aeab81c5` under `.tmp/`. Every build, probe run and gate `scripts/capped`;
the builds, the elaboration A/B and the gate sequential under the box-wide lock (never taken over). No edit to the candidate
or `main`; no merge; no push. Scope: the brief's eight attacks. Evidence: `docs/evidence/2026-10-03_panic-preprint-audit/`
(small; the scratch `.tmp/` probe fixtures, wires, mutant copies and the main archive deleted at the end).

## Verdict

**MERGE-CLEAN.** No member outside gc's permitted set and no gc behaviour missing from a membership set was found in 68 probes
beyond the lane's 21 rows (51 + 5 stdlib + 12 method-set corner cases, main vs candidate vs go1.26.5; one of them undecided on
BOTH sides because the harness refuses gc's double concurrent report): every candidate answer either matched gc exactly, admitted gc's draw inside an enumerated set whose other members are gc-realizable identity
assignments, or REFUSED BY NAME (BUG-099 / unpinned family / frontend quarantine); `main` refuses every one of them. The two
implementation refinements are faithful and semantically inert (one extra machine step per called method; no budget row moved
— the gate's baseline diff at the tip is exactly the 5a row). The three posed statement changes were unpinned, are each
exactly the settled premise the new `Config.abort?` demands, and every pinned `_stmt` and the coherence theorems are
byte-identical in statement. BridgeSet rows 155–173 are load-bearing (two one-token mutants → two type mismatches). The pool
refuses the phase's collision draw and the enumerator carries it. The findings below are LOW/records-level; none changes a
verdict or touches runtime code before merge — F5 (the language-coverage ledger's §8 totals, which the gate's own
reconciler flags) is the one records correction to make at or before the landing.

## Findings (by severity)

**F1 — LOW (elaboration margin, G-C3 decision 6).** Re-measured back to back under the lock (alternating, two runs each,
`evidence/elab-ab.tsv`): `PrefixFacts` **1.48× / 1.48×** (14.48 → 21.46 s, 14.77 → 21.81 s; the lane measured 1.44×),
`MachineSound` 1.23× / 1.25× (62.4 → 76.6 s; lane 1.17×), `StepErrors` 1.16× / 1.18× (199.7 → 231.7 s; lane 1.16×),
`StringPanic` 0.80× / 0.72× (faster), the rest 0.98–1.06×. No module crosses the 1.5× stop, but `PrefixFacts` sits within
2 % of it on both runs. The whole increase is `simp` (profiler cumulative 19.1 s → 32.6 s; tactic execution and type checking
flat): the `fun_cases` sweeps `stepFn_picks_none` / `stepFn_picks_some` over seven more arms plus the two `.stop`-arm record
lemmas (`stepPanicStop_picks_none/_some`). Not a stop and not a fix-first item — but the NEXT arm-adding lane should expect
this module to cross the rule unless the sweep is restructured (a generic lemma for the catch-all positions, as the
`picks_entry_none` macro already does for the entry arms). Recorded so the ceiling is visible before it is hit.

**F2 — LOW (refusal text accuracy, records).** `preprintFatalStop`'s runtime-error refusal names «runtime.errorString for a
nil dereference, runtime.plainError for panicwrap». gc's concrete type set for a runtime-error payload raised INSIDE the method
is wider: `panic(nil)` inside `Error()` prints `panic while printing panic value: type *runtime.PanicNilError` (probe
`method-panics-nil`, `evidence/gc-first-lines.tsv`); an index fault would print `runtime.boundsError`, a failed assertion
`*runtime.TypeAssertionError`. The refusal is honest and by name (BUG-099's class) and the row is red as designed; only the
enumerating text under-describes the class. Suggest «gc prints its concrete runtime-error type (errorString, plainError,
*PanicNilError, boundsError, …)» in `preprintFatalStop` and BUG-099's note at or after the landing.

**F3 — LOW (a pre-existing gap, narrowed by the lane, not closed; NOT reproduced).** `splitNewestPending?` treats an
`.unrecorded` entry (a carrier with no method-set record, BUG-053) as settled, so if such an entry is NOT the head, a method
gc might call on it is silently never called and the head renders; only an `.unrecorded` HEAD refuses (`abortRefusal`). The
observable would be the method's side effects (output), not the first line. Reachability: `rewriteMark` yields `.unrecorded`
only for a `.defined`/`.sync` carrier absent from `ctx.methodSets`; every user type the frontend lowers carries a record, and
I could not construct such a payload through the frontend — flagged from the definitions, not exhibited. `main` never called
any method, so the class is pre-existing and strictly smaller after the lane. A one-line fail-closed strengthening is
available if wanted: the phase's cursor refusing at `.stop` on any `.unrecorded` entry («whether gc calls a method here cannot
be decided»). Optional; records the hole.

**F4 — LOW (unpinned fatal families, follow-up candidates).** A method panicking with a pointer-typed payload refuses as
«payload family not pinned … (dynamic type *main.inner2)» where gc prints the mechanical `type *main.inner2`; likewise a basic
payload (`type int`). Design decision 4 pinned exactly the string and display-named defined families; these refusals are by
name and name the dynamic type. Cheap widenings (`"type " ++ <display of a pointer/basic type>`) for a follow-up, not defects.

**F5 — LOW (records completeness; the gate's report-only reconciler flags it HIGH).** `docs/language-coverage-ledger.md` §8 still
reads «All numbers at the current tracked baseline (3800 cases, 3563 PASS / 237 FAIL …)» while the lane re-pinned the baseline to
3821 / 3584 / 237; `tools/reconcile-records` (the `cross-ledger reconciliation` step, REPORT-ONLY) prints «[01] C4 HIGH the
language-coverage ledger §8 arithmetic is computed over a STALE baseline … (delta: 21 cases, 0 reds)» at the tip
(`evidence/ci-diff-tip-tail.txt`). The previous re-pinning lanes (5b, C4) carried a §8 movement line (`3799 + 1 = 3800; …`); this
lane's 2 flips + 21 born rows have none. Records only — add the §8 paragraph/movement line (3800 + 21 = 3821; 3563 + 2 + 19 =
3584; 237 − 2 + 2 = 237; the two BUG-099 reds on a named row) at or before the landing.

**F6 — INFO (records wording).** Handoff §3 heads the three changes «internal — not pinned in `BridgeSet`». True of `main`'s
rows (grep empty for all three), but the NEW form of `step_abort_elim` IS now pinned as row 170 (and `step_stop_unsettled` as
171) — the sentence reads as if it stays unpinned. One clause («… now pinned in their new form, rows 170–171») would make the
record exact. `stringPanicEntry?_some` is in the core audit's required list by NAME only; its statement was never pinned.

**F7 — INFO (positive, bounds the §6 follow-up).** The handoff's library-reach concern («`errors.New`'s `Error()` body may be
absent from a reachability-pruned wire») did not bite for the two commonest idioms: `panic(errors.New("lib"))` → `lib`,
`panic(fmt.Errorf("w: %d", 3))` → `w: 3`, and the recovered `errors.New` box re-panicked (members=2, gc's member 0) all PASS on
the candidate (`evidence/probe-results.tsv`, stdlib rows). The follow-up stays open for bodies reached only through a payload
in a package the reach set prunes; it is not blocking raft's `panic(err)` shape.

## What was checked, by attack

1. **Faithful to gc** (`deps/go/src/runtime/panic.go:702`–`:755` at the pin re-read; `printpanicval`/`printanycustomtype` in
   `error.go`). The walk, the `error`-before-`stringer` order, the newest→oldest call order (observed through state as well as
   `println`: `state-order-across-methods`, `newest-mutates-oldest`), post-defer state through a pointer receiver, named results
   modified by the method's own defers, the method's own `recover()` (direct → nil; deferred → recovers only the method's
   panic, named result honoured; a recovered inner panic returning the zero string → gc's `panic: ` with an EMPTY line = the
   machine's `{"message":""}`, `evidence/empty-result-adhoc.txt`), the fatal for a panic inside the method (string first line,
   defined type by display name — including a defined STRING type `type main.dstr2` and an error-typed payload whose own
   `Error()` is NOT called, `method-panics-error-typed`; a deferred panic after a normal return), defined non-struct carriers
   (string/slice/map/func/bool/float/array types), pointer vs value receivers (`mix-value` → `S`, `mix-pointer` → `E`;
   `value-receiver-on-ptr`; `stringer-ptr-receiver`; `error-wins-ptr`), promotion (through an embedded interface field — the
   `.iface` dispatch anchor — and through nil/non-nil embedded pointers), interface payloads (`var err error = …`, an
   interface embedding `error`), and multi-panic chains (string/error mixes either way; three distinct; non-adjacent equal
   entries never collapse). Identity: the per-pair draw's envelope at THREE identical entries is exactly the 4 observations gc's
   walk can produce under some box assignment (one call collapsed; two calls collapsed; two calls `[recovered]`; three calls)
   and gc exhibits member 0 (`evidence/membership-sets.txt`); distinct TYPES with equal fields and distinct POINTERS to equal
   pointees never draw (strict PASS); a struct with a slice field and a map payload re-panicked through `recover` collapse
   (gc member 0 ∈ set); equal payloads built at run time (two boxes in gc) → gc member 1 ∈ set; an unrecovered string head
   above an identical pair (members differ in the call count only); the ABORT's own head draw after the phase settled a newer
   error entry (`head-draw-after-phase`). Method-set corners (set 2, `evidence/probe-results-set2.tsv`): an AMBIGUOUS promoted `Error()` (two embedded fields at the
   same depth) is not in the method set — gc prints the struct's address form, the machine REFUSES (never calls either); the
   shallower promotion wins (`a`); `Error()` ambiguous but `String()` unique → gc rewrites through `String()` and so does the
   machine (`s`); a direct `String()` beside a promoted `Error()` → `Error()` (`a`); promotion through a non-nil embedded pointer
   (`z`), through an embedded local interface (`s`); a pointer-receiver method promoted into a VALUE's set through an embedded
   pointer (`po`) but NOT through an embedded value (gc address form, machine refuses; the pointer has it, `po`); a `**T`
   payload and a func-typed FIELD named `Error` have no method (gc address form, machine refuses). 7 PASS, 4 honest refusals,
   1 undecided (below). Typed-nil receivers: both BUG-099 rows refuse by name with the BUG-099 text; so does the embedded-nil-interface and
   the embedded-nil-pointer-with-value-receiver shapes (gc: `runtime.errorString` — the wrapper's own dereference, not
   `panicwrap`). Blocking: alone → the bare deadlock line (lane row); a goroutine's method blocking while main blocks → deadlock
   (`goroutine-method-blocks-deadlock`); woken by another goroutine → `woken`. `os.Exit` inside the method and `runtime.Goexit`
   during the panic are frontend-quarantined (`os`/`runtime` not modeled) — not probe-able, listed under "could not verify".
   `main` refuses all 51 set-1, 5 stdlib and 12 set-2 rows (`FAIL/lean-observation`, `membership` or `confluent`), as expected.
2. **The two refinements.** The split (P1 consult+select at `.stop`, P2 resolve at the frame's `.next`, P3 store at `.retV`)
   adds exactly one step per called method over the note's count; the `(older, entry, newer)` split is the chain by
   `splitNewestPending?_eq` (row 156). No semantic consequence: the gate's differential at the tip reproduces the lane's
   3583 / 238 with the baseline drift EXACTLY the 5a row; every `nonterm=`/`work=`/`depth=`/`backedge=` row keeps its
   baseline status (`scripts/coverage-baseline-diff --full` on my run, `evidence/ci-diff-tip-tail.txt`).
3. **The three posed statement changes** (`evidence/statement-check.txt`). None was pinned in `main`'s `BridgeSet` (grep
   empty), none is in the logic side's asks (their §4 asks for «rendering equations for error payloads, like the existing
   `StringPanic` lemmas» — delivered as rows 158–162), and `docs/changelog/61958f2e-WINDOW.md` lists them as internal. Each is
   minimal: the settled premise is exactly what `Config.abort?`'s new equation (row 155) requires; `stringPanicEntry?`'s erasure
   premise (`.none`, `false`) is sound because the phase never marks a string entry (a collision needs equal values, hence
   equal types, hence a pending — never a string — older neighbour) and `stringPanicEntries?_typed` carries the two conjuncts.
   The `Tests/StringPanicMembers` generic theorems gain the same settled premise. `GoLean/GoCore/ExecutionStatement.lean` is
   byte-identical (`git diff --stat` empty); `BridgeSet.lean`'s diff is additions only (header + rows 155–173).
4. **Coherence/totality.** `Step` 127 → 134 (the seven `preprint*` constructors), `Frame` 33, `FrameClass.preprint` classified
   by hand (the exhaustive `Frame.class`), `signalRefusal`'s arm named. Statements of `stepFn_sound`, `step_complete`,
   `stepFn_strict`, `stepFn_no_stray_panic`, `stepFn_picks_none/_some`, `stepFn_consumption_none/_some`, `step_preserves_wf_loc`,
   `stepFn_oblivious`, `MultiSound.stepFn_abort` byte-identical main vs candidate; `classification`/`run_panic_iff`/
   `finish_abort_step` are `_stmt`s in the unchanged file. No `sorry`/`native_decide`/`axiom` in `GoLean/`; no `maxHeartbeats`
   line in the diff; the core audit's required list +20 (counted) and the gate's core-audit step ok. BridgeSet rows real:
   `evidence/bridgeset-mutants.txt`. The `*_text` equations state what the logic side asked: `renderPanicHead_text` is the
   `StringPanic` shape with `rewritableBox first.value ∧ first.rewrite = .done text` as the payload premise, through to
   `runConfig_text_abort(_refused)`.
5. **The pool.** `poolThreadOblivious` returns `false` on `consumesRepanicCollapse` (the phase's collision, fail closed) and
   `stepThread_oblivious` carries the case; `innerVecs`/`EnumDedup` already refused the shape by name. Probed: a non-main
   goroutine panicking with an error payload (confluent, |set|=1 over all schedules), the same goroutine re-panicking the same
   box (`goroutine-repanic-same-box`: the enumerator carries the draw, members=2, gc ∈), main's method woken by a sibling, a
   sibling blocked (lane row). Two goroutines panicking with error payloads concurrently (set 2, `two-goroutines-panic-error`)
   is UNDECIDED on both sides: gc's stderr carries two concurrent panic reports (`CALLED:m`, `CALLED:g`, `panic: m`, then the
   second goroutine's report) and the harness refuses to classify it («additional or unknown report boundary after selected
   origin, refused») — a harness refusal, not a machine answer.
6. **Zero unplanned change.** `baselines/native-full.tsv` diff = header + the 2 flips in place + 21 born rows; 3800 + 21 =
   3821; the gate's re-pin guard: 0 PASS→non-PASS; `check-frontend-pins`: twin byte-identical; the certified row's set
   identical (the 5a line is provenance, `STALE certification: changed dependency … ChoiceTrace.lean`). The lane's whole-corpus
   choice trace (26445 identical dump rows outside the 23 lane ids) was read, not re-run.
7. **Elaboration**: F1.
8. **Gate**: `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the tip under the lock (04:48–05:03 UTC, 916 s wall) —
   RESULT FAIL on exactly the 5a pair: 37 steps ok, 2 FAIL (`certificate provenance`: STALE certification, changed dependency
   `ChoiceTrace.lean`; `baseline diff`: the one drift line `imported-goose/channel/google-search`); 3821 run = 3583 / 238; re-pin
   guard 0 PASS→non-PASS with the two GREENED notes; the report-only reconciler's C4 line is F5 (`evidence/ci-diff-tip-tail.txt`).

## Could not verify

- `os.Exit` inside `Error()` (probe p16's silent exit 3) and `runtime.Goexit` from a deferred call during an error panic
  (gc's `goexit` entries in `printpanics`): the `os`/`runtime` package surfaces are frontend-quarantined — refused by name, no
  machine answer to compare.
- An `.unrecorded` carrier in a non-head position (F3): not constructible through the frontend in this session.
- A method returning invalid UTF-8: not expressible as a row (the expectation cannot carry raw bytes); covered by construction
  (`renderPanicRewrite`'s `.done` arm routes through `stringFirstLine?`; `Tests/PanicRendering` pins `(boxed (.done ⟨#[0xff]⟩))
  .isNone`) — the D5 refusal class, not re-exhibited here.
- Two goroutines panicking with error payloads concurrently: the harness refuses gc's double report (above); the machine's
  enumerated set for the row was not compared.
- The lane's whole-corpus choice trace and its gc fixture check were read, not re-run (the gate's differential re-ran the corpus).
