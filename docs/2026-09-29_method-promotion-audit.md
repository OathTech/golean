# Pre-merge adversarial audit — lane `core/method-promotion-0928` (window row 3, native method promotion, G-P)

[AGENT] auditor, 2026-09-29, under the [USER]'s every-merge-audited rule (relayed). Candidate tip `a8741c9d`
(S0 `74f5bada`, S1 `ef015501`, S2 `5749ed35`, S3 `a8741c9d`), branched off `89792db1`; main at `4e7272b3`
(3 records-only commits ahead, train r54; `git merge-tree` clean). Specification: the ten decisions of
`docs/2026-09-28_gp-method-promotion-design.md` §6 (G-P PASSED, [USER] 2026-09-28, relayed). No edit to the
candidate or main; audit branch `review/method-promotion-0928`. Evidence (small):
`docs/evidence/2026-09-29_method-promotion-audit/`.

## Verdict: FIX-FIRST (records only; no wrong answer found)

The implementation matches the ten decisions: every probe agrees with gc go1.26.5, and the independent choice
trace is byte-identical except for the one documented row. One behaviour change is outside the design's
documented set, and it is not recorded anywhere (F1). The design's §5 criterion says «Anything else that moves is
a finding and stops the slice», so F1 has to be recorded before the merge. F1 moves toward gc, so it needs a
record, not a code change. F2 and F3 are text fixes. The rest is information.

## Findings

**F1 (MEDIUM) — an unrecorded behaviour change: a nil pointer box dispatching to a promoted declaration-only
STUB in the value set.** On main the promoted sync-primitive stub and the FR-23 stub were ordinary `Func`s
(`syncPromotedStub`/`promotedSigStub`). They were NOT marked `"wrapper": true`: only `synthesizeWrapper` set it,
at `emit.go:6298` on main. `nilValueMethodText?` therefore put them in BUG-087's panicwrap family. Witness
`probe-nil-stub.go` (`type S struct{ *sync.Mutex }`, `var l Locker = (*S)(nil); l.Lock()`):
- **main** consumes one `nilValueMethodText` pick. Under `--choices 1` it panics
  «value method main.S.Lock called using nil *S pointer».
- **tip** consumes nothing and admits the nil-dereference text only.
- **gc** gives the nil-dereference text 20/20.

The tip is the right answer: the stub's wrappee is the embedded `*sync.Mutex`, not `S`, so gc's `methodWrapper`
test fails. Main's width-2 envelope here was a latent over-width in BUG-087. But this is a change to an admitted
set and to a consumption count. It is not S8, and it is not the step-count shift. No corpus row covers it; the
lane's whole-corpus trace could not see it. The handoff's claim «the `nilValueMethodText` consumption count is
unchanged (S9)» holds for the corpus only. Required: a born row for this shape (PASS at the tip), a BUG-087 (or
new BUG) paragraph naming main's over-width as a wrong envelope fixed by S2, and a changelog/handoff line.
[AGENT] view: no [USER] ruling is needed beyond the record, because this fixes an over-wide envelope that no
ruling covers. The same mechanism also dropped the stub entry's whole-pointee READ before the refusal for a
non-nil box (handoff choice (iii)). That shortens the access trace before a refusal and is fail-closed; it should
be named in the same record.

**F2 (LOW) — `Cont.frame`'s `fid`: the docstring and changelog claim is false for one frame.** The docstring
(`Machine.lean`, `Cont.frame`) and the changelog row say the field is «the FUNCTION WHOSE BODY THIS FRAME RUNS …
never an interface anchor or a record». The spawn's `Entry.again` barrier frame
`.frame [] [] [] [(cv, [])] .stop fid` (`Multi.lean:655`) runs no body. It carries the `go` statement's callee
id: the interface anchor for `go i.M()`, and for `go S.M(s)` over a promoted embedded-interface record, the
record's key `methodFuncId S M`, which names no `Func`. The handoff's wording «the anchor the go statement
re-dispatches through» is also inaccurate: the re-dispatch anchor is the pending call's `cv`, not `fid`. The field
is representation only, so behaviour is unaffected. Every other entry path sets `func.id` of the entered target:
- call positions, through `Entry.callConfig`;
- defer drains, normal and panic, and the spawn's `run` arm, through `Entry.drainConfig`;
- dispatch, method expressions over declared or promoted callees, and closures;
- the drivers: the entry function / `pkgInitFuncId`.

Fix: state the exception, or name that frame by a stated rule.

**F3 (LOW) — `findFunctionIn?_filter`'s migration reading is overstated.** The lemma is true for any `p`, and
BridgeSet row 68 has teeth. It answers the logic team's request 5 in the abstract. The docstring and changelog say
the post-P table IS the pin's table filtered by «the retired `¬ Func.wrapper`». That is inaccurate. The promoted
stubs also left the table, and they were non-wrapper `Func`s: 62 in the corpus; in the twin,
`raft.MemoryStorage.{Lock,TryLock,Unlock}`. Measured on the twin: `funcs` 450 is identical, and `methods`
537 → 481 is main's list minus the 53 wrappers minus the 3 stubs, order preserved. So the filter is
«¬wrapper ∧ ¬promoted-stub». A client crossing pins also crosses a `Func` shape change: the field was removed.
Fix: the wording.

**F4 (LOW, procedural) — `noodler/frontier/promoted-method-expression-ptr` FAIL → PASS is decision 5's class.**
The row is `(*Out).Get` over a promoted value method. It has the same shape as the born
`embedding/promoted-ptr-method-expression/promoted-value`. The tip returns 4, as gc does; main refused it at the
frontend (FR-3). Decision 5's text («the `(*S).M` deref-adapter refusal retires for PROMOTED entries») covers it
necessarily, and this audit's trace confirms that no other row moved. Procedurally, though, §5's criterion listed
only S8 and step counts and said an unlisted movement «stops the slice». The lane re-pinned with a written reason
and continued, reporting the flip for the audit. [AGENT] view: covered in substance; the [USER] should
acknowledge it at sign-off, and no separate ruling is needed.

**F5 (INFO) — `go i.M()`: the path is walked at the spawn step.** The walk runs against the spawn step's store
and its reads are attributed to the child (the pre-existing spawn-entry model). The retired wrapper walked the
path in the child's own later steps, and so does gc. The difference is observable only in racy executions. The
race verdicts are preserved (`probe-spawn-race.go`: pointer-field and pointee writes after `go` are race on main
and tip, 5/5 under gc `-race`). The DRF control flips from race on main (over-refusal) to ok 5 at the tip: a
spawn instance of decision 6 that is not in the corpus. Suggest born rows.

**F6 (INFO) — the decoder trusts a stub record's `sig`; only `sig.id = member` is checked.** A record whose
`sig` disagrees with its target `Func` is accepted (mutant `a9b`). Its calls refuse by name, but satisfaction
reads the forged `sig`. This is the same trust the retired stub `Func`'s own signature carried. Optional
hardening: compare `sig` with the target's `Func` when that `Func` is present. The shadowed-target mutant `a3`
(a valid path to the shallower-shadowed `base.own`) is also accepted; that is decision 2 by design.

**F7 (INFO) — the merge mechanics.** The branch is 3 records commits behind main, so `--ff-only` needs a rebase
and a re-gate (protocol step 5). After the rebase, the row-3 changelog section falls under r54's «Scope of this
changelog» paragraph (logic team request 8). The section should say that the frontend flags, the
`decodeProgram` signature and `RunResult` did not change, and that the wire schema did (v1 → v2, v1 refused).

## The ten decisions (each checked against the code, with witnesses)

| # | Verdict | Witness |
|---|---|---|
| 1 static selectors untouched | holds | the frontend diff hunks touch only the wrapper synthesis → `promotionRecords`, the stub emitters, and `emitSelector`'s method-expression arm; `promotedReceiverArg` and the call/method-value lowering are unchanged |
| 2 `go/types` records, validated, refusals by name | holds | 15 audit mutants (`decoder-mutants.tsv`): wrong/short path, cycle-shaped owner, absent local target, non-promoted member, unsupported without sig, sig id, forged record on an imported sync type, iface adjust, extra key, empty path → all refused by name; missing records for used promotions → run-time `stuck` naming the missing method; `a3`/`a9` accepted by design (F6) |
| 3 walk at call start (child / drain / per call) | holds | S0 rows; `recover/p4`, `p12` (interface method values); `nilpath/q20` (child aborts); F5 nuance for `go` |
| 4 nil points; iface tail re-dispatch as its own step, `stepFn` total | holds | `nilpath/q14`–`q19` = gc; `q8`/`q13` chained panic through the iface tail at the drain = main; `Entry.again` delivers `.retV (.funcVal …) (.callValCalleeK …)` / re-queues on the draining frame; `stepFn` structural (core audit, no `partial`) |
| 5 method expressions call the record | holds | `recover/p2` (iface tail), `p5` (`(*SP).rw`, refused on main, 0 = gc at tip), `nilpath/q16`–`q19` |
| 6 exact loads on embedded-pointer hops | holds | `receiverAt_ptr_deref` pinned (mutating the trace order fails the build); the ci differential; `spawn/*` |
| 7 `recoverAtDeferred` preserves eligibility | holds | 11 recover probes (value, pointer and iface embeds; iface-then-promoted; method expression with iface tail; two-level; interface method value; `(*S).M`; the not-directly-deferred negatives `p6`/`p7`; a second recover) = gc and = main |
| 8 step/fuel shift only | holds | trace dumps byte-identical (the step count is not a trace column); `spawnPromotedPteeRace` has a smaller enumeration tree with the same verdict |
| 9 wire v2 | holds | `wrapper` key and v1 schema refused by name (gate controls); `promotions` required; twin `0b58402a…` with the written reason in `check-frontend-pins` |
| 10 plan S0–S3 | holds | four slices, gates recorded; post-gate edits are records only and disclosed (S0 ledger token, S1 records, S2 C5 token + records, S3 records). This audit's gate ran at the committed tip |

## The flagged items

- (a) **The absent-target acceptance is sound and fails closed.** It applies only when the last hop reaches an
  opaque declaration (TypeDef kind `unsupported`: imported named types and the FR-23/FR-25 markers; no local
  type is emitted that way) AND the key is exactly `methodFuncId reached member`. Mutant `a4` (local reached
  type) and `a11` (sync-typed reached field) refuse. A call through the record refuses by name; the retired
  wrapper went `stuck`. It is a record-level rule beyond the design's letter, but within decision 2 and the
  design's §3 table («twin `log.output` stays (log, output)»). It is not a widening: the retired wrapper stood for
  the same entry. Satisfaction through such a record answers false where the wrapper answered with its own
  signature. This is unobservable, because only package `log`'s interfaces could require the unexported
  `output`.
- (b) F4. (c) F2.
- (d) **The re-worded FR-23 cause is truthful.** «promoted method T.M (promoted signature does not lower: …)» is
  emitted only when the signature probe fails. No tracked consumer used the old text outside dated evidence, and
  `perdecl_kill_test` asserts the substrings.
- (e) **The stub nil-first order matches the retired stub entry's auto-deref.** It keeps the `.nil` panic and
  refuses `inPtrSetOnly` entries. The dropped read is in F1.
- (f) **The other implementer choices are sound.** The `Entry` shapes, the decoder-added marker, the defaulted
  `ofTables` and the `reachability.py` label resolution were checked. The `Mem.loadFor l l` → `Mem.load l` swap
  on the declared arm is definitionally the same.

## The frame field ([USER]-ruled), coherence, pins

- **`fid` at every entry path:** see F2.
- **Pinned lemmas:**
  - `Entry.callConfig_run`, `frame_exit_returns` and `enterFrame_declared` are pinned (rows 65–67) and required.
  - `enterFrame_declared` states exactly the function-call rule, with no dispatch and an empty trace.
  - The request-5 lemmas `enterFrame_declared`, `receiverAt_nil_path` (identity, plus the `_deref` half) and
    `resolveMethod?_declared` state what the team asked. `findFunctionIn?_filter`: see F3.
- **BridgeSet rows 65–89 are real statements:** five one-edit mutants (rows 67, 68, 76, 80, 84) fail to
  elaborate, and the unmutated copy passes (`bridgeset-mutations.txt`).
- **Coherence and totality:**
  - The gate reports: core totality audit 110 required theorems, classical trio only, and engine-isolation ok.
  - `ExecutionStatement.lean` and `Prefix.lean` are untouched, and the gate built them, so packet A/B are still
    proved as stated.
  - The escape-hatch scans are clean. No `sorry`, `axiom` or `native_decide` was added, and no `partial` appears
    in `GoLean/GoCore/`.

## Zero unplanned behaviour change (independent)

- **Gate differential:** 3784 = 3548 / 236 against the baseline 3549 / 235. The one difference is the stale
  certified record `imported-goose/channel/google-search` (5a). There were no other flips. The baseline's four
  FAIL → PASS rows are the three predicted plus the noodler row.
- **Choice trace, main `4e7272b3` against the tip.** Each side used its own frontend and binary; the run was
  `--dump`, 6 streams, 878 ids. The set includes 84 promoted/embedding ids, 155 interfaces, 57 methods, 79 race
  and 63 goroutines. The dumps are BYTE-IDENTICAL (8107 rows). The results are identical except the six stream
  rows of `noodler/frontier/promoted-method-expression-ptr` (`unsupported` → `ok`). The export refusals are
  identical. See `choice-trace-compare.txt` and `choice-trace-ids.txt`.
- **Probes outside the corpus:** F1, and F5's DRF control (decision 6's class).
- **Raft probes:** logger-installed PASS on both sides, identical; logger-teeth identical on both sides; the
  `twin-single` driver PASSes at the tip (`raft-and-twin.txt`).

## Records

- **Changelog:** the migration table names a replacement for every retired helper (`Func.wrapper`, the frame
  marker, `concreteMethodForDynamic?`, `concreteMethodSignature?`, `dispatchLeaf`/`wrapperForwardArg`/
  `recvFieldChain`, `Cont.recoverTransparent`/`recoverThroughWrappers`, the callee lookup).
- **BUGS:** BUG-041's Cases line now holds only `race/free/array-dyn-index-read-write`; the bug-index
  cross-check in the gate is ok.
- **Handoff:** it is honest about the post-gate edits, and it poses the flagged items itself. F1 is the one
  movement it did not see.

## Gate

Under the lock: `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` at `a8741c9d`. RESULT: FAIL, EXIT 1,
953 s. It is red on EXACTLY the 5a pair: `certificate provenance` STALE (C9: `GoLean/CLI.lean`) and the baseline
drift `imported-goose/channel/google-search` PASS → FAIL (certified record wire-sha256 STALE). Every other step
is ok, including 110 required theorems, eval 298 ok, negative 394 matched, wire boundary and frontend pins. The
reconciler has 2 report-only findings: C9, and C13, which predates this lane. Tail: `gate-ci-slow-tail.txt`.

## Not verified

- The chdriver twin (`probeTwinChoice`) and the elect group under the machine (40–65 min each). Neither the lane
  nor this audit ran them.
- Only 878 of the 3784 ids were traced; the lane traced all of them.
- Detector-soundness was not re-run.
- The lane's per-row step counts were not re-derived.
- The 5a re-certification is the train's job.

## Re-verification (`ddf62818`, 2026-09-29)

[AGENT] auditor, at the coordinator's request (relayed). The fix round is on `core/method-promotion-0928` at
`ddf62818`, rebased onto main `4e7272b3`: the four slices, then `17416d2c` (fixes) and `ddf62818` (records). The
pre-rebase tip is `refs/snapshots/method-promotion-fix/pre-rebase` = `a8741c9d`. This branch was rebased onto
`ddf62818`. Evidence: `docs/evidence/2026-09-29_method-promotion-audit/reverify-*`.

**REVISED VERDICT: FIX-FIRST, one small records item (R1). Every other claim is verified; F1–F3, F5 and F7 are
closed, F4 awaits the [USER]'s acknowledgement as posed, and F6 is recorded.**

- **Rebase:** `git range-diff 89792db1..a8741c9d 4e7272b3..6b6352b5` shows all four slices `=`, so the
  rebased patches are identical. The fix commits' `GoLean/` changes are docstrings and comments only, in
  `Machine.lean`, `Multi.lean` and `Syntax.lean`.
- **F1 closed.** The born rows behave as claimed:
  - `embedding/promoted-stub-dispatch/{nil-box-sync-stub,nil-box-sync-stub-itab}` PASS/confluent at the tip.
  - The same rows FAIL on main («enumerated observation set has 2 member(s)»).
  - gc gives nil-deref 5/5 under each of plain, `-race`, `-gcflags=-l` and `-gcflags=-N -l`, in both shapes.
  - The BUG-087 paragraph, its Status clause and its Cases line are present and accurate.
  - The handoff's §1 S2 claim now reads «over the CORPUS».

  **FR-35 is a pre-existing gap, correctly rowed.** Interface dispatch to a promoted sync primitive has refused by
  name since that earlier arc's audit-fix-round F4 stub, on main and the tip alike. Decision 9 / design §4 keep
  the sync stubs as `unsupported` records, so modelling the dispatch was outside P's ruled scope.
  `box-sync-stub` is FAIL on both sides. `box-sync-stub-race` answers `race` on main on 3 of 6 streams, via the
  retired whole-pointee read, and `unsupported` at the tip: the dropped read, fail-closed, as recorded.
- **R1 (LOW, new): the «FR-23 nil-box variant cannot be rowed» claim is false.** The claim sits in the BUG-087
  paragraph and the handoff. A method whose opaque type appears only as a PARAMETER is callable with `nil`, and
  the caller lowers:
  - The probe `reverify-probe-fr23.go`, subject `takeNil`, is `var t T = (*S)(nil); t.Take(nil)`, where `Take`
    takes an `iter.Seq[int]` and is promoted through `*In`.
  - gc gives nil-deref 5/5 under all four flags.
  - Main admits {nil-deref, «value method main.S.Take called using nil *S pointer»} and consumes one
    `nilValueMethodText` pick.
  - The tip gives nil-deref only, with no pick.

  So the tip is right, and this is the FR-23 half of F1's class. Fix: correct the sentence and birth the row. It
  is PASS at the tip and red on main.
- **F2 closed.** The `Cont.frame` docstring, the `spawnStep` comment and the changelog now state the exception
  exactly. The spawn's `Entry.again` barrier frame runs no body and carries the `go` statement's own callee id: the
  anchor, or the record key, which names no `Func`. The target's frame (`func.id`) is pushed on top when the
  pending call drains. The timing claim is confirmed in `spawnStep`:
  - `enterFramePickV` at the spawn walks the path up to the embedded interface field.
  - It returns `Entry.again anchor [fieldValue, …]`.
  - `drainConfig` builds `.frame [] [] [] [(cv, [])] .stop fid`.
  - The concrete target is resolved only when the child's first step enters the anchor through
    `frameDeferFall`.

  One precision note: the field's value (the box) is already in hand at the spawn, but resolving it to a target
  happens later. «not known» means «not yet resolved», which is accurate enough.
- **F3 closed.** The docstring and changelog now say 53 wrappers plus 3 stubs removed, order kept; twin `methods`
  537 → 481 and `funcs` 450 unchanged. This matches this audit's measurement.
- **F5 closed.**
  - `race/free/promoted-spawn-disjoint` is PASS/confluent at the tip. On main it FAILs with a machine-side status
    divergence (race).
  - `race/negative/promoted-spawn-ptr-field` is PASS/racy on both sides.
  - gc agrees, per the round-1 probes of the same shapes: `-race` clean 5/5, and race 5/5.
- **F7 closed.** The rebase is clean. The changelog's tool-interface scope was spot-checked by diff:
  - `decodeProgram : Json → Except String Program` has the same signature, now at `NativeToIR.lean:3263`.
  - The only change to `tools/nativefrontend/main.go` is the schema name in a comment.
  - `lean-toolchain`, `lake-manifest.json`, `scripts/diff-coverage` and `scripts/coverage-manifest` are
    untouched.
- **Baseline:** the header reads 3790 = 3553 / 237, and the ledger tally 130 + 9 + 25 + 8 + 65 = 237 matches it.
  **Gate:** under the lock, `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at `ddf62818` gave RESULT
  FAIL, EXIT 1, in 1391 s. It is red on EXACTLY the 5a pair: `certificate provenance` STALE and
  `imported-goose/channel/google-search` PASS → FAIL. The differential is 3790 = 3552 / 238, with no other drift;
  110 required theorems, eval 298 ok (`reverify-gate-ci-diff-tail.txt`).
- **Choice trace, the worker's caveats closed.** Main `4e7272b3` was archive-built: `lake build golean` replayed
  106 jobs from a trace-verified warm cache, and nothing came from the primary checkout. The run covered the 878
  round-1 ids plus the 6 born ids. Dumps and results are byte-identical except for:
  - the born ids: main's `nilValueMethodText` consumptions on the two nil rows; the tip's post-refusal pool
    picks on `promoted-spawn-disjoint`; `box-sync-stub-race` race → unsupported;
  - the noodler row.

  The export refusals are identical (`reverify-choice-trace.txt`).
- **Not verified:** the chdriver twin and the elect group under the machine (unchanged from round 1). Only 884
  ids were re-traced, not the whole corpus.
