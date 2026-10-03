# Batched window review — 2026-10-03

[AGENT review] Independent review requested by the user. The builder's brief and the lane
handoffs were treated as claims to check, not evidence of correctness. No implementation,
baseline, main checkout, or builder lane was changed. This report lives in the separate
`review/window-1003` worktree, based on main.

Reviewed snapshots (all line references below are to these snapshots):

| Name | Commit | Scope |
|---|---|---|
| M | `3bb8f4fc9cd7dab16571787140731b6d4c1f9d0e` | Active primary branch, `main`; all landed window steps |
| D | `9c14fef18823807fd026eab90372c1b910471851` | Unlanded `window/packet-d-equations-1003`; inspected and tested in an owned detached scratch worktree |
| Customer pin | `61958f2ee03047d13fec320266be22a1a759075c` | Starting point of the promised migration record |

Unqualified references mean M. References marked D mean the candidate, not code already on main.
Lean basenames in the tables are under `GoLean/GoCore/`.

**Disposition: changes requested before calling the window complete or offering Packet D.**
The core and its baseline gates passed the checks below. I found no new executable mismatch
in the interaction probes and no contradiction in the five execution bridges. I found two
reproducible defects in Packet D's acceptance evidence, an unaccounted charter work item,
and a small cumulative changelog omission. These do not establish a false kernel theorem
or an unsound interpreter. The final offer also has recorded work still pending.

## Findings, ranked

### F1 — P2: the write-survives-panic client theorem has an impossible premise

**Witness:** D `Tests/EquationClient.lean:120`, especially `:124` and `:125`;
`GoLean/GoCore/Machine.lean:3364`, `:3376`, `:3383`, `:3437`, `:4694`.
The contradicted acceptance claim is D `docs/changelog/61958f2e-WINDOW.md:266`;
the requirement is `docs/codex-briefs/2026-09-24_packet-D-equations.md:47`.

`fact_write_survives_panic` assumes
`abortMsg ctx (panicEntryOf ctx (.string txt)) [] 0 = .ok t`. Its panic argument is
`.stringLit txt`, so the chain contains the **unboxed** `.string txt`. `panicPayload`
does not box it. `rewriteMark` returns `.none`, and the renderer handles string payloads
under `.interface .string`, not this value. Thus the premise is false for *every*
`ctx`, `txt`, and `t`; the final step refuses. The theorem cannot witness any aborted run.

This kernel-checked witness compiled at D, independently of the client's proof:

```lean
import GoLean.GoCore.Equations
open GoLean GoLean.GoCore GoLean.GoCore.Machine

example (ctx : ProgramCtx) (txt : GoString) :
    renderPanicPayload ctx (panicEntryOf ctx (.string txt)) = none := rfl

example (ctx : ProgramCtx) (txt : GoString) (t : String)
    (hmsg : abortMsg ctx (panicEntryOf ctx (.string txt)) [] 0 = .ok t) : False := by
  cases hmsg
```

The full scratch witness also proves the actual `stepFn` result is the named unsupported
rendering refusal, and has a successful boxed-`"boom"` rendering control. Separately,
the client's sequence contains a direct panic, **no callee call**, despite its docstring
at `:114` and the required write-then-callee-panic scenario. A valid arbitrary-renderer
premise is useful; an unsatisfiable one does not exercise the failure-state interface.

**Requested correction:** use a renderable boxed argument, actually enter and unwind a
callee, and instantiate the complete fact with satisfiable memory/entry/rendering premises.
Keep the symbolic theorem, but add a concrete inhabitation check so this acceptance case
cannot silently become vacuous. This finding does not refute `Prefix.run_panic_iff` or
`Finish`'s retention of the endpoint store.

### F2 — P2: the no-unfold gate accepts unfolding hidden in a local theorem

**Witness:** D `Tests/EquationClient.lean:2074`, `:2093`, `:2122`, `:2142`;
D `scripts/check-equations:22`, `:33`, `:70`.

The check visits only immediate `Tests.EquationClient.fact_*` declarations. It scans and
rechecks their proof terms, but a referenced constant is a leaf: the body of a private or
non-`fact_*` helper is never checked. Marking `stepFn` irreducible while checking the caller
does not invalidate an opaque theorem already proved by reducing `stepFn`.

Reproducer at D: insert this helper in the client's `Facts` section, before FACT 1:

```lean
private theorem returnViaReduction (s : Store) (env : LocalEnv)
    (k : Cont) (ch : Choices) :
    stepFn ctx s (.exec .returnStmt env k) ch =
      .ok (.signal .ret k, s, ch, silent) := by
  rfl
```

In `fact_call_then_return`, replace the first `rw [hbody]; simp only [stepFn_eqns]`
with `rw [hbody]; exact returnViaReduction _ _ _ _`. Leave the gate's bypass anchor,
all pins, and all other facts intact. **The complete `scripts/check-equations` exits 0**:
292 pins, 11 facts, “none unfolds stepFn”, and all nine negative controls pass. The
helper's `rfl` does unfold `stepFn`. The experiment ran only in the owned scratch D
checkout; the original source was restored and the client rebuilt afterwards.

**Impact:** this gate can report that the consumer uses only the published equation
interface when it depends on interpreter reduction through a helper. It checks kernel
validity, but does not fully enforce the advertised independence/usability contract.

**Requested correction:** inspect the proof dependency closure of client-owned helpers,
using the supported equation/prefix API as the boundary, and add the indirect helper
case as a negative control. This is a test-contract gap, not an axiom-audit bypass.

### F3 — P2: the CL1–CL5 corpus commitment has no completion or limit accounting

**Witness:** `docs/2026-09-23_batched-window-charter.md:123`;
`docs/2026-09-24_window-plan.md:44`; the live completion entries at D
`docs/changelog/61958f2e-WINDOW.md:253` and `:266`.

The execution table still assigns five corpus lanes: the customer's method/multi-field
shape, byte decoding plus nil-map behavior, write/call/unwind and observation-before-failure,
slice/ring aliasing, and callback/Storage/timer boundaries. The reviewed handoffs and
rulings neither map these lanes to completed differential rows nor explicitly defer them.
The changelog accounts for the core steps through 7a but does not close this row.

This is **not** a claim that these language features have no tests. There are substantial
method, slice, panic and callback suites. For example,
`Corpus/coverage/exec/binary/little-endian/main.go:33` exercises the heartbeat context
shape and `:46` tests one short read; it does not itself establish the full promised
nil/empty/map-preservation and lengths-1–7 case matrix. The twin and individual lane
audits likewise do not supply that matrix. The extra review probes below provide some
interaction evidence, but are not tracked corpus lanes or downstream proofs.

**Requested correction:** give CL1–CL5 an explicit disposition, with existing case IDs
and uncovered subconditions. Add only genuinely missing cases, or state the remaining
scope as an offer limit. Do not mark the whole charter delivered merely because all
serial core units have landed.

### F4 — P3: the cumulative tool-interface changelog misses `--unseq-census`

**Witness:** `tools/nativefrontend/main.go:87`; D
`docs/changelog/61958f2e-WINDOW.md:13`, `:197`, `:274`;
`docs/2026-09-28_note-from-logic-team.md:68`.

Comparing the customer's pin to M adds the frontend's `--unseq-census` flag. It emits
a TSV census instead of a wire. The cumulative changelog has no entry for it: its initial
inventory explicitly used the `GoLean/` diff, and the later “flags unchanged” entries
are scoped to their individual lanes. Those lane statements can be true while the
pin-to-offer record is incomplete.

**Requested correction:** include this additive flag in the final cumulative tool table.
The Lean toolchain and Go pin are unchanged in the same comparison; the decoder's wire
acceptance changes are already documented. This omission does not break an existing
invocation, and is lower priority than F1–F3.

## Execution-statement fidelity

The five requested corrections are implemented in M and survive D. The declared `_stmt`
Props are not being mistaken for proofs: `Prefix.lean` discharges them and `BridgeSet`
pins the resulting theorems.

| Logic-team correction | Checked implementation and qualification |
|---|---|
| Retain failure state and residual choices | `ExecutionStatement.lean:85` puts both in every `FinishOutcome`; `:120` gives the finishing transition; `Prefix.lean:456` proves `run_panic_iff`. The CLI still projects away this state on failure; a consumer obtains it through the prefix/finish relation. F1 concerns the test, not these definitions. |
| Terminal rendering and consultation are real operations | `Finish.aborted`/`abortRefused` at `ExecutionStatement.lean:126` require `abort?`, `consumeAtE` and the fallible `abortMsg`. The preprint phase must settle before `abort?` succeeds. Renderer refusal remains a separate case; it is not silently treated as Go panic. |
| Prefixes and exact fuel boundaries | `Prefix` at `ExecutionStatement.lean:72` allows arbitrary endpoints; `LRun` at `:145` is derived. `ZeroCost` at `:64` covers normal stop and four blocked forms. `run_ok_iff`, `run_panic_iff`, `run_deadlock_iff`, `run_fuelOut_iff` retain 0-cost classification versus the abort's extra step. Fuel-out concerns the fixed tape's actual prefix, not a quantification over completed runs. |
| Replay by records, with coverage | `replays` at `ExecutionStatement.lean:158`, `Prefix.finish_replay` at `Prefix.lean:252`, and `replay_coverage` at `:311` connect site/bound/pick to the actual consultation. The bound-≤1 and empty-tape conventions remain explicit. D folds the premise-free consumption theorem back into `MachineSound` and retargets pin 62 without changing its statement. |
| Unconditional refusal-separated bridge | `ClassRefusal`/`classification_stmt` at `ExecutionStatement.lean:357`/`:369`, proved at `Prefix.lean:536`; `classification_wf` is the domain corollary. `NoRefusal` at `ExecutionStatement.lean:169` quantifies over all initial tapes and excludes zero-cost endpoints. It is sequential-only and is not implied by `StateWf` alone. |

Labels are the ordered `{trace, picks, out}` channels (`Ops.lean:2121`). The fold and
silent law (`Ops.lean:2132`, `:2138`) preserve the empty observation; no total ordering
between channels is promised. The frame carries the declared `FuncId`, and
`Machine.lean:7283` exposes `frame_exit_returns`: clients can inspect call/return state
without a Raft-specific label. `out` is printed output, not a `Ready` event.

D's `PoolProjection` extends the singleton result to output and terminal projections,
including fatal results (`PoolProjection.lean:389`, `:406`, `:486`). The general budget
is `fuel + seqOpCount`; the equal-fuel theorem has a reachable-no-boundary premise
(`:514`, `:550`, `:560`). It does not claim unconditional equal fuel. Deadlock and
refusals remain excluded from `transferableWide`; a pool can resume an artificial
wake-ready blocked seed that the sequential driver classifies as deadlock.

## Charter and late-request accounting

| Charter unit or condition | Disposition at the reviewed tips |
|---|---|
| 0a, production frontend inventory | Delivered historically at `3fb4a0d1`; repeated here against M for the same pinned 14 fixtures and 8 generated variants, including decoder acceptance and counter controls. This is lowering evidence, not customer proof acceptance. |
| 0b/A, stable statements and live records | Delivered: M has 173 numbered BridgeSet rows; D has 501. No facade, Iris rules, or runtime dependency on the toy client was added. Changelog is still a draft, with F4 to close. |
| E6a | Delivered, including non-main-unit lowering, the scoped failing-occurrence trigger, decoder checks, status-diverse corpus row and twin re-pin. The full grammar/legacy retirement is not represented as complete. |
| E6b–E6e | Explicitly removed from the critical path by the 09-27 ruling, recorded in `docs/2026-09-24_window-plan.md:75` and the changelog at `:76`; the logic team's 09-28 acknowledgement accepts the surviving legacy triple. This is a stated limit, not a missing authorized retirement. |
| Label and packet B | Delivered with the five corrections above. Successful setup remains a premise, init-time printing is refused, and full pool/registry coverage remains owed. |
| P, methods | Native declaration/promotion path replaces wrappers. `enterFrame_declared` (`Machine.lean:7257`), receiver-path equations (`Ops.lean:3592`), and `resolveMethod?_declared` are pinned. The narrowed lookup is backed by `findFunctionIn?_filter` (`Syntax.lean:1249`), under its predicate premise. Receiver capture/copying, nil handling and direct recover were checked against code, gates and the interaction cases below. |
| C3, continuations | `Cont := List Frame`, with the old names as pattern abbreviations and list laws, is delivered. This supplies no context-fill law. Its laws are pinned in rows 90–107; later preprint adds its own frame. |
| B6, numeric locals | Delivered: `VarId := Nat` (`Syntax.lean:23`), `LocalName` at `:39`, `Func.localName?` at `:896`; `Func.localsOk` and its coverage/kind lemmas (`Locals.lean:121`). The decoder checks scope, spelling and table consistency. Activation slot lemmas are separate from lexical IDs. Table positions are metadata, not a proof of source provenance, and IDs are not stable across edits. |
| Native Intn addition | Delivered as a named choice site with the normal bound-1 no-consumption rule. Package `math/rand.Intn` and `math/rand/v2.IntN` are bound; method forms, crypto/big restoration and additional random APIs are explicitly limited. The narrower D1–D8 disposition is ratified in `2026-09-30_intn-pick-handoff.md:100`; do not infer all originally listed callees are implemented. |
| C4, block allocation | Delivered with explicit `entrySlot` (`Machine.lean:7557`), shifts/lookups, normalization (`:7595`, `:7669`), distinct activation slots (`:7740`), saved defer values versus captured locations (`:7748`, `:7758`), and store-neutral lexical exit (`StepFn.lean:1162`). Source initializers remain at their source execution points. Freshness composes with heap monotonicity (`StateWf.lean:8508`). |
| C4 preservation scope | The escape audit and scoped injection/stuttering claim are recorded in `2026-10-01_gc4-block-allocation-design.md:36` and `:57`. That document explicitly says the run-level simulation is **not a theorem** (`:67`). Raw location JSON is a ruled standing limit (`:141`); pointer equality/aliasing is not discarded. Changed fuel/allocation order and the separately ruled try-lock search cap are disclosed. |
| Panic preprint, BUG-004 item 4 | Delivered before D. Error/Stringer dispatch uses ordinary frames, after defers; its new phase, fatal behavior, choice consultations and rendering limits are documented and reflected in the new equations. The interaction probes exercise it with P/B6/C4, not just in isolation. |
| 7a, packet D | Present on D only. Equations, setup, unwinding, projections, pins and gate exist. F1/F2 prevent accepting the client evidence as claimed. The partial memory interface is explicitly disclosed, below. |
| 7b, final re-pin offer | Still open: exact offer commit/tag, final certification/gates and sign-offs. D's candidate-freeze line names its proof-content commit `4a4f381f`; it is explicitly not a final offer tag. |
| CL1–CL5 | Unaccounted completion/limit disposition: F3. Existing corpus coverage is not denied. |
| Other deferrals | NaN, typed profiles, the Language spike, full registry/pool coverage, the independent-occurrence commutation theorem and the access-granularity/NPDRF obligation remain explicitly deferred or parked (`docs/2026-09-23_batched-window-charter.md:136`). The withdrawn unrestricted unseq-confluence claim is not used to justify determinism. |

All nine requests in the 09-28 note were checked separately:

| Request | Result |
|---|---|
| 1. Equations reaching memory laws; `.retV` filing correction | **Partial, with explicit limit.** D has variable/root-result reads, plain/chain stores, and entry allocation equations reaching `loadRoot`, `storeLoc`, `Store.alloc`. Pointer, field, index and map reads still stop at `applyStrictOp`/`applyRhsOp` (`Equations.lean:862`, `:1028`). The candidate handoff at `:216` and changelog row 7a say so. These inner equations remain migration work for the customer's record/pointer proofs; do not advertise the whole request as discharged. The call/defer/statement-operation arms are correctly filed under `.retV`. |
| 2. No-globals/no-initializer setup equation | D `Equations.lean:1441`, with argument/result layout at `:1471`, `:1487`, `:1502`, `:1518`, is pinned. Lookup, arity, reserved types, binding, allocation and result-location premises are visible; choices are unchanged. General initialization/output correctness is not claimed. |
| 3. Lean name table and runtime slots | B6 pins 108–132 and the activation lookup laws supply the interface described above; no identification of a lexical ID with one permanent heap cell. |
| 4. C4 layout/lifetimes | `entrySlot` and the laws listed above provide the requested compositional pieces. The fresh-activation result assumes the intervening heap-size inequality; it is not an unconditional native-lowering theorem. |
| 5. P entry pins and lookup | Delivered in pins 65–89, including the named entry/receiver/resolution equations and lookup-filter laws. Declared non-wrapper lookup preservation carries the stated predicate assumptions. |
| 6. Callee identity at exit | Delivered as frame `fid` and `frame_exit_returns`, not as an additional output event. |
| 7. Stable unwinding equations | D has sequence/block glue, unrecovered resume, `deferPanic` entry and empty-defer-frame stripping, including preprint arms (`Equations.lean`'s `panicking_*`, `next_panicResumeK_*`, `frameExit_*`). |
| 8. Tool-interface changelog | Wire v1→v2→v3 and decoder acceptance changes are recorded; `decodeProgram`, `RunResult`, Lean and Go pins are addressed. Cumulative frontend flag delta remains F4. |
| 9. Singleton embedding without a supplied `seqOpCount = 0` | D proves the count-zero consequence of the no-boundary premise and supplies narrow and wide equal-fuel forms. Full pool/registry support is still a separate obligation. |

## Consistency and offer conditions

The D additions comprise **292 equation pins and 36 projection pins**, all unique and all
present in `Tests/GoCoreAudit.lean`'s required theorem list. Numbered BridgeSet rows 1–501
have no gaps or duplicates. The compiled audit checks 535 required theorems at D versus
207 at M. The 328 added requirements agree with the 328 added pins. The equation client
also checks every one of its 292 pin types against the corresponding equation theorem.
The gate lives in the test/library graph, and the default core build imports BridgeSet.

The existing pins' statements survive D; row 62 changes its target from the copied
`PrefixFacts.stepFn_consumption_some'` to `MachineSound.stepFn_consumption_some`, dropping
the latter's unused premise. The migration note names both changes. Changelog rows are
historical deltas with explicit before-tips; earlier constructor counts and line numbers
must not be read as claims about the final shape.

In addition to fixing/dispositioning the findings, the offer must retain these recorded conditions:

- D has not landed or received train step 5a. Its handoff records CI red on certification
  staleness, not a fresh green offer receipt. This review's main `--diff` PASS does not
  certify the different D commit. The final `--slow`, release check, exact freeze/tag and
  applicable sign-offs remain necessary (`docs/2026-09-24_window-plan.md:43`).
- The G-C3 elaboration exception is **pending**, not approved. D's handoff at `:156` and
  `:162` reports BridgeSet at 1.81×, then about 2.1 seconds after further pins, and poses
  an exemption for additive pin growth. I did not rerun that benchmark or grant the exception.
- D's proposed CLAUDE wording (`docs/2026-10-03_packet-d-handoff.md:192`) is a draft requiring its recorded
  approval. Main still says singleton output/terminal work is owed, consistently with D
  not yet being landed. The proposed update must retain setup, init-print and pool limits.
- The memory-floor limit above belongs in the actual offer. Broader slice backing/path and
  disjoint-update laws remain later work, not an implicit promise that all helpers are opaque
  to the customer after this re-pin.
- No downstream `scripts/check` or proof migration was performed. The source-only inventory
  below does not stand in for the customer's acceptance. No merge, tag, or push was performed.

## Validation and reproducible evidence

Builds/gates ran through `scripts/capped`, with 48 GiB cap and four Lean threads, under
an atomic `mkdir /home/dev/projects/golean/artifacts/build-lock.d`. Each owned lock had
an owner record and was released by its owning wrapper. No live lock was taken over.
Scratch and copied build caches are under the review worktree or its `.tmp/packet-d`;
the primary checkout and builder lane stayed unchanged.

| Check | Snapshot | Result |
|---|---|---|
| `scripts/ci --diff` | M | **Exit 0, PASS**, 997 seconds. 298 eval tests; 3,821 differential rows = 3,584 PASS / 237 existing FAIL, all matching baseline; 394 negative rows match. Slow-tier cases use cached certified records in this mode, not a fresh `--slow` recertification. |
| `scripts/check-equations` | D, original | **Exit 0**, 292 equation pins, 11 facts, nine controls. F1/F2 explain the limits of this green result. |
| `scripts/check-core-audit` | D | **Exit 0**, 54 GoLean modules (45 GoCore), 535 required theorems, 19,861 local declarations; classical trio only; five compiled poison controls rejected. |
| F1 Lean witness | D | **Exit 0**; impossible premise and actual refusal proved, boxed-string positive rendering control proved. |
| F2 complete equation gate on indirect-helper mutant | Owned scratch D only | **Exit 0 unexpectedly**, with all nine controls green. Original source restored; `lake build EquationTests` then **exit 0**. |
| 15 new interaction probes | M | All export and execute. Go/Lean terminal kind, preceding output and first panic line match for each; no unsupported/stuck result counted as a match. Seven normal and eight panic cases. |
| Customer lowering inventory | M frontend, historical customer source | 22/22 export and decode; 1,066 recursively counted statement nodes; zero graphs and zero legacy probes. Counter positive controls detect graphs and occurrence kinds. |

The CI metadata says `git_dirty=true` because the owned review checkout had an untracked
`deps` symlink to the existing reference checkouts. No tracked source differed from M
during that run. Accordingly this is a review run with identified source content, not
a new clean-commit certification receipt. CI's report-only reconciler also reports the
standing C13 item: 79 patch-version mentions across ten documents, zero HIGH findings.

Review-run build receipt: inputs SHA-256
`7302b01d4fe686973bc36087802ae3f01277dad21b4303adfb012cccac4703d0`, binary SHA-256
`445878f1caf3b7d7043109218d54601dc969373bb65cbe795513ed1a9b65004f`.
Toolchain: `leanprover/lean4:v4.32.2`, Go `go1.26.5 linux/amd64`.

The 15 probes combine steps as follows (all scratch, not additions to the corpus):

| Cases | Interaction checked |
|---|---|
| `value-copy-preprint`, `pointer-preprint`, `preprint-embedded-interface` | Promotion/receiver copying or live pointer capture, deferred mutation, then panic Error-method dispatch |
| `preprint-own-recovery`, `promoted-recover` | Named results, direct recovery in promoted methods, deferred control and preprint frames |
| `preprint-method-capture`, `method-capture-lifetimes`, `preprint-map-closure` | Numeric locals, repeated block activations, captured cells/method values and later reads |
| `preprint-write-call-panic` | Callee write, deferred increment, then terminal rendering observes the updated value (42) |
| `block-aliases`, `shadow-defer-result`, `nested-loop-temps` | Distinct cells, preserved aliases, shadowing, named results, nested loops and continue |
| `multi-field-wrap` | Unrelated field preserved, two method calls, uint64 wrap and Boolean result |
| `preprint-intn-one`, `rand-repeated` | Native Intn bound-1 behavior and supported draws inside or beside the new phase; no statistical/PRNG claim |

The customer inventory uses source
`b2c37c1492a16de317de40b2c487f478c8b9c6a1`, copied read-only with `git archive`, and
the same eight-variant generator as the historical inventory. Production frontend
built from M: SHA-256 `169d49b42313df88689a1c2bb28458fed196c8a2aac432e6629a9ffd2c843f40`.
Every wire was retained in owned scratch. The CLI decoder was checked by looking up
a deliberately absent function: all 22 reached the expected function-not-found result
after decoding, rather than failing wire admission. That diagnostic is not an execution PASS.

| Unit | Statement nodes | Export/decode | Graphs / legacy probes |
|---|---:|---|---|
| callchain | 10 | OK | 0 / 0 |
| e1 | 49 | OK | 0 / 0 |
| e1-equivalent | 49 | OK | 0 / 0 |
| e1-local | 62 | OK | 0 / 0 |
| e1-wrong | 49 | OK | 0 / 0 |
| error-string | 10 | OK | 0 / 0 |
| f1 | 45 | OK | 0 / 0 |
| f1-alternative | 45 | OK | 0 / 0 |
| f1-s-local | 49 | OK | 0 / 0 |
| f1-s-results | 45 | OK | 0 / 0 |
| f1-s-wrong-target | 45 | OK | 0 / 0 |
| f2 | 57 | OK | 0 / 0 |
| recovery | 16 | OK | 0 / 0 |
| shared | 69 | OK | 0 / 0 |
| f2-proof-positive-block-fallthrough | 59 | OK | 0 / 0 |
| f2-proof-positive-closure | 58 | OK | 0 / 0 |
| f2-proof-positive-declare-after-defer | 59 | OK | 0 / 0 |
| f2-proof-positive-declare-before-defer | 59 | OK | 0 / 0 |
| f2-proof-positive-set | 60 | OK | 0 / 0 |
| f2-proof-wrong-capture-target | 57 | OK | 0 / 0 |
| f2-proof-wrong-helper-value | 57 | OK | 0 / 0 |
| f2-proof-wrong-shared-order | 57 | OK | 0 / 0 |

The same walker reports `len-vs-call-order` = **13 graphs / 6 probes** and
`e13-sibling-panic-order` = **60 / 9**, with populated `eval`, `invoke`, `allocate`,
`guard`, `wide`, `recv`, `target`, and `load` counts across the controls. Thus the zeros
above are not a counter silently ignoring graph nodes. This repeats the original
source-pin inventory against the current frontend; it does not inventory subsequent
customer source changes or discharge their current proof migration.

Local reproduction material is retained under this worktree's `.tmp/`: `run-locked`,
`review-ci-diff.log`, `run-probes.py`, `window-probes/`, `inventory-controls.py`, and
`packet-d/.tmp/{VacuousPanic.lean,IndirectUnfold.lean,probe-indirect.py,review-equations.log,
review-core-audit.log,review-vacuous.log,review-indirect-gate.log,review-restored-client.log}`.
The two compact defect reproductions are also given inline above so the findings do
not depend on retaining build artifacts. Review scope ends at these snapshots; no
later fix, downstream acceptance, final certification, or performance exemption is assumed.
