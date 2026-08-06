# Channels/goroutines arc — design of record (2026-08-06)

Status: DECIDED (user sign-off 2026-08-06) — resolves the options paper
`docs/2026-08-06_concurrency-arc-options.md` (D1–D9); the six research
notes `docs/2026-08-06_concurrency-research-*.md` are the evidence
base. THE DECIDING PRINCIPLE, set by the user: every contested choice
is resolved for *what supports growing toward a fully faithful Go
semantics while preserving differential testing* — grow by EXTENSION
(new registry entries, new edge sources, additive quantifiers), never
by REVISION (step-granularity changes, theorem restatement). This
principle is itself binding on future arcs touching this machinery.

## Decisions

**D1 — Machine shape: ThreadPool over the unchanged sequential
machine.** `MultiConfig {threads : Array Config, shared : ExecState}`;
per-thread `Config` and `ExecState` unchanged. The Prop relation stays
per-thread with a spawn component; iris-lean's thread-pool `Language`
supplies interleaving (already instantiated sequentially in
`proofs/GoLeanProofs/Lang.lean`). Threads carry stable goroutine IDs
(pool position is not identity). Rejected: coarse-only ground truth
(unsound without the reduction theorem it would presuppose);
logic-only pool (fails executability — the foundational requirement).

**D2+D3 — THE SYNCHRONIZATION-OP REGISTRY (one mechanism, two duties).**
The scheduling-point set and the happens-before edge-source set are the
same set: synchronization operations. The registry initially contains:
channel send/recv/close, select, `go` spawn, goroutine exit. Each entry
is simultaneously
  (a) a SCHEDULING POINT — the scheduler `Choices` site (pick ∈
      [0,|runnable|)) is consumed ONLY at registry ops and ONLY when
      |runnable| > 1 (critical: `Choices.consume` pops even at bound 1,
      so unconditional consumption would desynchronize every existing
      adversarial-stream run; sequential conservation depends on this);
  (b) an HB EDGE SOURCE — segment-level happens-before race detection:
      execution between registry ops is a SEGMENT; the machine records
      per-segment read/write sets at `Loc`-path granularity through the
      existing `loadLoc`/`storeLoc` chokepoint; vector clocks over
      goroutines advance on registry-op HB edges (per the memory
      model's channel rules); a conflict between HB-unordered segments
      ⇒ terminal `raceDetected` — races FAIL CLOSED per run, on every
      run, deterministically given the stream.
Growth contract: a future sync primitive (atomics, Mutex, Once,
WaitGroup) is added by REGISTERING it — one scheduling point + one HB
edge rule — with no change to the scheme, the sequential machine, or
existing statements. The detector's HB skeleton is TSan's, keeping the
in-machine classification structurally aligned with the `go run -race`
external oracle as both grow.
Soundness obligation (recorded, owed in slice 3): the NPDRF-style
reduction — DRF programs behave identically under registry-point
scheduling and full interleaving (ICTAC 2018; Lipton movers; CHESS
architecture) — with the self-enforcing coupling that programs outside
DRF are exactly those the machine refuses. Per-construct mover lemmas
for coarse steps (appendSlice-class) are the granularity ledger's
formal successor. Rejected: naMode two-step accesses (grows by
revision: changes sequential step granularity/fuel today, changes
decomposition per future access class; detection by exploration luck
weakens the differential lane).

**D4 — Envelopes** (the doctrine's statements, shipped with their
sites): L1 interleaving — envelope = all schedules over runnable
threads (spec has zero scheduling text; pure omission latitude); L2
select — "any entry-ready case" (spec's "uniform pseudo-random"
deliberately weakened per the possibilistic doctrine; NO
re-randomization on the blocked path — probe-pinned; wake-order
latitude is L1/L4); L4 waiter pairing — "any matching waiter" (no spec
text; gc's FIFO wakeup is a membership point, and real FIFO would
force queue state into channels — rejected). Buffer FIFO is SPEC
("Channels act as first-in-first-out queues") — deterministic, strict
lane. Channel panics (send-on-closed, close-of-closed/nil, make
negative) are real recoverable Go panics — diverging from Goose's UB;
more faithful and differentially testable.

**D5 — Fairness: the additive-quantifier path.** Now: ∀-stream
`Terminates` for the blocking-discipline class — the strongest claim,
assumption-free, true because the scheduler picks among RUNNABLE
goroutines and starvation requires a runnable spinner (not expressible
race-free without atomics; to be made precise in slice 2's note).
Later (atomics arc): `FairStream` — prefix-decidable bounded-starvation
predicate, Simuliris-style first-order trace fairness, TCB-clean —
added as an ADDITIVE weaker quantifier for the larger class; existing
theorems never restated. Any `Fair` assumption is ABOVE-SPEC (Go
promises no fairness) and must carry a statement caveat. Fallback
recorded: Perennial claims no termination at all.

**D6 — Main-exit**: modeled faithfully — main's return terminates the
program (goroutines killed); partial goroutine leaks are observably
nothing in Go (exit 0) — model-side classification only, spec-side
join discipline. Deadlock ("all goroutines are asleep") is a terminal
fatal classification matching Go's runtime, differentially testable
(go exits 2); the -race and deadlock-detector oracle modes are
mutually exclusive (probed) — the harness must never combine them.

**D7 — Channels**: primitive heap-cell `chanData` (the `mapData`
precedent — locSup/StateWf/gen_heap reuse verbatim). Blocked
goroutines are blocked-Config shapes; NO waiter queues in channel
state; rendezvous = a pairing step (direct handoff, matching gc);
`cap=0 ⟺ unbuffered` is one rule. Select: entry-time operand
evaluation (order spec-pinned), one readiness step, L2 choice among
ready; default-with-none-ready deterministic, consumes nothing.

**D8 — Statement idiom**: carrier swap (`execStmt`→`execProg`).
`GoSpecC`: single-threaded `InitialSplit` pre; post over the JOINED
final state, `.mainNormal`-pinned; ∀ one stream (schedules + latitude
unified — the single-stream design independently validated by Coyote's
recorded-global-order architecture). `ProgressExecC` excludes
`deadlocked` and `raceDetected`: a proven spec implies deadlock- and
race-freedom on every modeled schedule. Channel facts exported as
operational history predicates; Iris strictly internal (iris-lean
ready: concurrent WP/fork/invariants/adequacy at the pinned rev; no
prophecies needed — primitive channels make lifting laws the atomic
specs). `MultiConfig`/scheduler/`chanData` enter the statement TCB with
readability-as-specification review; GoSpecC/ProgressExecC join the
designated set with first-order readouts; Comparator landmark at the
first designated-statement change.

**D9 — Validation: the six-lane taxonomy** (validation note §4):
(a) sequential-degenerate — existing 1027 cases bit-identical, by
construction of D2(a); the conservation theorem
`execProg_single_eq_execStmt` is the transfer lemma keeping all 33
designated sequential statements valid unrestated.
(b) CONFLUENT — the membership singleton-failure rule inverts into a
pass precondition: enumerator certifies |set|=1 over all schedules,
then strict go-run equality — full-strength differential verification
for deterministic concurrent programs.
(c) schedule-dependent — membership lane; enumerator = interleaving
explorer at registry granularity (tractable at litmus scale, the right
scale: enumeration validates the MODEL, not targets); DPOR pruning and
PCT stream-sampling are later additive layers (recorded).
(d) racy-negative — every enumerated path refuses; `-race` red
justifies (TSan: no false positives); `-race`-green + our refusal =
three-way investigation.
(e) litmus pairs — channel-synchronized form admits exactly SC
outcomes / racy form refuses: the DRF-SC boundary pinned executably.
(f) deadlock/leak — deadlock differential; leak self-consistency.
Doctrine updates: `-race` becomes a default membership sample source
(probes: plain go-run is a point-mass — 0/700 on a depth-1 corner;
-race 6/6 orderings); per-lane epistemic captions ship with the lanes.

**Prior art posture**: Perennial's in-tree etcd-raft verification
(driving their 2025-26 channel rewrite) is a standing comparison point;
their spec-sentence-keyed channel tests are imported as fresh canonical
corpus inputs with provenance. Their differential apparatus is deleted
upstream — executable validation is this project's differentiator.

## Slice plan

1. **Channels-only, zero scheduler** — `chanData` + make/send/recv/
   close/len/cap/range/select-with-default as machine steps; blocking =
   immediate deadlock terminal; flips all 38 `channels/` cases (all
   single-goroutine — machine-shape §6) into the strict lane. Fail
   closed: `go`, sync.*, multi-ready select, `go` in `$pkginit`.
2. **Goroutines + ThreadPool** — spawn/exit, scheduler site, deadlock
   terminal, main-exit, sequential-conservation theorem, GoSpecC/
   ProgressExecC + a fork/join headline witness. Comparator landmark.
3. **The registry's second duty** — segment-HB race detection,
   racy-negative lane, litmus pairs, the NPDRF reduction obligation +
   mover lemmas.
4. **Select multi-ready + wake-order membership + confluent lane** —
   enumerator over schedules, envelope statements live.
5. **Iris proof layer** — concurrent WP over the relation, channel
   invariants/ghost, the GoSpecC witness proved.
6. **Doctrine/harness updates** — -race sampling, lane captions,
   envelope-width review.
Owed early probes (slice 2/3 entry): iris-lean ghost ergonomics under
real protocols; waiter-wake observability at scale; mover-lemma
difficulty on appendSlice; nil-mixed select corners.

## Slice-1 build log (2026-08-06, branch `channels-arc-s1`)

Executed as decided (channels-only, zero scheduler, zero new `Choices`
sites). Decisions made DURING the build, recorded here:

- **Range-over-channel is a frontend/decoder DESUGAR, not a machine
  frame** (deviation from the machine-shape note §6's "dedicated
  iteration frame in the `mapIterK` mold"): a channel range is exactly
  repeated comma-ok receive until closed-and-drained, and the index-able
  ranges already desugar to `while` — only `mapRange` is primitive, for
  its nondeterministic order. The desugar lives in `decodeRange`'s
  `"chan"` kind (fresh `$rcoll`/`$rrecv`/`$rok` cells; per-iteration
  fresh user variable; `break`/`continue`/labels via the ordinary loop
  machinery). This also avoids a blocked-RANGE Config shape whose
  slice-2 resume semantics would have been bespoke.
- **`SelectClauseHead` + `Array (SelectClauseHead × Stmt)`** rather than
  a mutual `Stmt`/clause inductive: the `Prod`-nested shape is the
  `arrayLit`/`mapData` precedent and keeps `Stmt` a plain nested
  inductive (no mutual-`deriving` risk on the heavily-proved syntax
  type).
- **Channel ops are ONE new `Cont` family** (`chanStK`, mirroring
  `stmtOpK`'s target-checked operand discipline) ending in `applyChanOp
  : … → Except GoError (Config × ExecState)` — the apply's outcome is a
  CONFIGURATION because a channel op may proceed, panic, or BLOCK.
  Select adds `selectOpsK` (entry-time operands, spec step 1) +
  `applySelect` (readiness/commit, step 2-3) + `selectRecvK`
  (post-selection targets, step 4). Select recv clauses always target
  fresh frontend temps; user LHS (including `:=` declares and effectful
  index expressions) becomes a body-side assignment, which is what makes
  step 4's "LHS after communication" hold structurally.
- **Blocked configurations** `.blockedSend/.blockedRecv/.blockedSelect`
  are relation-SILENT (no outgoing per-goroutine rules — pairing is the
  slice-2 pool's job); `stepFn` and the drivers classify them as the new
  `GoError.deadlock` terminal (status `deadlock`, message the detector's
  fixed line), BEFORE the fuel check. Payloads carry what pairing needs
  (channel loc, in-flight value, target locs / evaluated clauses).
  OPEN for slice 2 (recorded): the pool's wake step for a blocked
  RECEIVE resumes by storing to the pinned locs + `.next k`; select
  wake commits against `.blockedSelect`'s evaluated clauses.
- **Panic-message narrowing** (L9): the channel panics carry gc's
  realized strings ("send on closed channel", "close of closed channel",
  "close of nil channel", "makechan: size out of range") as
  `runtimeErrorValue` payloads — the spec pins only THAT a run-time
  panic occurs; this matches the repo's standing makemap/makeslice
  narrowing and is what the differential compares.
- **Deadlock differential**: new `expected_status: deadlock`
  (coverage-manifest / diff-coverage / coverageharness) — go run must
  print the fixed `fatal error: all goroutines are asleep - deadlock!`;
  both sides compare the synthesized
  `{"status":"deadlock","message":"all goroutines are asleep -
  deadlock!"}` observation. Strict-lane only, and NEVER combined with
  `-race` (detector suppressed there — ground-truth note §5). The
  membership enumerator fails LOUD on a deadlock member (no silent
  handling).
- **Nil-channel canonicalization**: `normalizeValueForTyFuel` gained
  REAL chan arms (`.chan` passes, `.nil` → the canonical nil channel,
  else fail closed) — a raw untyped `return nil` at a channel-typed
  result otherwise reached channel ops as `.nil` (caught by
  select-deterministic/channel-operands-eval-order). Lockstep
  `isNormalForTyFuel` arms; congruence/locSup/soundness lemmas extended.
- **Receive vs. call ordering** (spec §Order of evaluation: calls AND
  receives are lexically ordered): a receive hoists to a statement, so
  `emitBinary` pre-binds its LEFT operand to a temp when the RIGHT
  operand contains a receive (caught by select-ready-send's
  `len(ch)*10 + <-ch`). KNOWN NARROWER SCOPE: call-ARGUMENT positions
  (`f(len(ch), <-ch)`) do not yet pre-bind — no corpus case pins the
  shape; a future one would fail visibly at the differential, never
  silently.
- **Interface-typed receive targets fail closed** in the `=` statement
  form (`x = <-ch` with `x` an interface and a non-interface element):
  the chan-recv statement stores the raw element value and carries no
  boxing wrap. The `:=` forms are unaffected (target typed at the
  element type). Precise unsup reason; no corpus case needs it.
- **Proof-repair shape** (the fun_cases positional-tag cost the
  machine-shape note §6 predicted): stepFn's new arms renumbered the
  correspondence proofs' `case caseN` tags; the mapping was recovered
  empirically (probe file over `fun_cases stepFn`) and the named
  handlers renamed; new explicit handlers were needed only for the
  chanRecv-entry plan match, the chan/select apply-panic arms, the
  plain-shift `if_neg`, and selectRecvFinish. `step_det` gained the
  `stmtPlan_of_chanPlan` disjointness lemma (the one generic-statement
  cross pair simp cannot refute). proofs/ changes are three mechanical
  repairs (step_det simp set, wp-law rule sweeps + `wp_init`'s
  `chanStFirst` refutation arm); NO designated statement changed.

Validation (corrected at the audit response — S5/S10: the original
paragraph undercounted 65/8 and omitted four flips and the 1047th
case): 5 new machine eval-test pins (82 total); full corpus 1047 exec
(after the multi-ready refusal pin below) + 311 negative; ALL 38
pre-existing `channels/` reds + 19 slice-1 guardrail pins + **12**
channel-blocked singletons (builtins/make-channel-len-cap,
control-flow/{break-label-select,goto-out-of-select},
generics/type-parameter-channel-ops, interfaces/typed-nil-channel,
maps/{channel-key,nil-channel-key,delete-nil-key-types,
nil-read-key-types}, scoping/select-clause-scope,
init/{quarantined-init-dep,quarantined-init-iface} — the last four
were quarantined solely on a chan type; this arc released the init/
quarantine) flipped FAIL→PASS — **69** flips, zero regressions;
baseline re-pinned from the full run in the flip commit. One
deliberate red-first pin landed after: `channels/select-multi-ready` —
the L2 multi-ready choice is REFUSED (fail closed) until slice 4.

### Audit response (2026-08-06, pre-merge audit of this slice)

Twelve confirmed findings (two refuted), all addressed on the branch —
guardrails first (12 new go-run-verified pins), then fixes:

- **BUG-022 (S1+S7, major)**: the receive STATEMENT inverted spec
  §Assignments' phases — target-address panics fired BEFORE the
  communication (Go receives first; drains the channel even when the
  store then panics; blocks — deadlock — where we panicked). Fixed by
  reordering the statement form to the select path's shape:
  `ChanStOp.recv` carries its targets, `applyChanOp` communicates
  first and delivers through `selectRecvK` (empty body); the
  target-first machinery was REMOVED, not left dead. Pins:
  `channels/recv-edge/*` (drain discriminators + the
  deadlock-not-panic classification).
- **BUG-023 (S2+S9, major)**: the receive hoist reordered ahead of
  inline `len(ch)` in every operand list except binary operands. Fixed
  with ONE mechanism replacing the binary-only pre-bind: `emitStmtList`
  flags statements whose operand sweep contains a receive
  (`stmtSweepContainsRecv`) and `emitBuiltin` hoists `len`/`cap` under
  the flag, restoring lexical order everywhere. Pins:
  `channels/recv-order/*` (five positions).
- **BUG-024 (S3+S8, major)**: bare `<-ch` statement emitted a wire node
  the decoder rejected — a whole-package `status:error` where the base
  per-decl-quarantined. Fixed: the ExprStmt arm emits the zero-target
  chan-recv (receive-and-discard). Pin: `channels/recv-stmt`.
- **S4/S11 (minor)**: `m[k] = <-ch` was refused with a misleading
  reason (and the naive dispatch reorder would have been a silent
  wrong answer — verifier's adjacent finding). Implemented instead:
  map-element receive targets pre-bind base/key in phase-1 order,
  receive into a temp, map-assign in phase 2. Pin:
  `channels/recv-map-elem` (`m[len(ch)] = <-ch`).
- **S6 (note)**: `defer close(ch)` implemented via a synthetic
  one-parameter closer through the existing defer machinery. Pin:
  `channels/close-edge/defer-close`.
- **S5/S10 (minor)**: this note's flip accounting corrected above
  (69/12, corpus 1047 at slice tip — 1059 after the audit pins).
- **S12 (note)**: terminal-class prose extended — `go_adequacy`'s scope
  caveat now names the blocked/deadlocked class (the guarantee got
  STRONGER); `Config.terminal`'s docstring records why blocked configs
  are deliberately not "finished" (slice 2's pool steps them);
  `enumRun`/`enumInitRun` classify blocked configurations as
  `deadlock` BEFORE the fuel check (the incidental fuel-out
  misclassification), and their docstring lists the new error class.

Interface-typed receive targets in the `=` statement form remain
fail-closed with a precise reason (unchanged narrow scope);
`m[k], ok = <-ch` comma-ok map-element forms ride the S4 arm.

### Delta-review response (2026-08-06, review of the audit-response commits)

Five confirmed findings on the audit-response delta, all fixed with
red-first pins (10 new, all go-run-verified):

- **BUG-026 (D2, critical)**: the BUG-023 per-statement receive flag
  was NARROWER than the binary pre-bind it deleted — for-init,
  for-cond (condPre), else-if chains, and switch case expressions
  reordered receives past inline `len(ch)` (silent wrong answers vs
  base), and the sweep's justifying comment ("for conditions are
  hoist-forbidden", D4) was false. Fixed by deleting the sweep and
  making the flag FUNCTION-scoped (`fnHasRecv`, set at emitFuncDecl /
  emitFuncLit / synthesizePkgInit): over-hoisting `len`/`cap` is
  unobservable (pure, non-panicking, lexically placed; condPre
  re-evaluates per iteration), so the coarse scope covers every
  statement-emission path — including future ones — by construction.
  Pins: `channels/recv-order/{for-init,for-cond,else-if,switch-case}`.
- **BUG-027 (D1, major)**: `$deferClose<N>` was unqualified while
  `liftSeq` resets per function — two `defer close` functions collided
  into a whole-package duplicate-id error. Fixed: qualified by the
  enclosing function like every lifted literal. Pins:
  `channels/defer-close-two/*` (including the unrelated-subject
  blast-radius companion).
- **BUG-025 (D3, minor — generalized by the verifier)**: spec
  §Assignments phase 2 is LEFT-TO-RIGHT; the machine's multi-target
  stores were all-or-nothing. The RECEIVE path is fixed (`selectRecvK`
  carries remaining delivery values and stores each target immediately
  as its address arrives; machine+stepFn lockstep) — pin
  `channels/recv-edge/second-target-panic-stores-first` green. The
  GENERAL path (plain multi-assign, pre-existing on main) is filed
  OPEN as BUG-025 with the still-red `multi-assign/store-order-plain`
  pin.
- **BUG-028 (D5, minor)**: map-element receive keys pre-bound a
  panicking non-call operand pre-receive (spec-unordered; gc drains
  first, and the sibling pointer/slice arm had just moved to
  communication-first). Fixed: base/key emit inline into the
  post-receive map-assign; calls and `len(ch)` keys stay pre-receive
  via the existing hoists. Pin:
  `channels/recv-map-elem/key-panic-drains`.

Final slice-tip counts: 1069 exec cases, 989 pass / 80 fail — the 78
pre-existing non-channel gaps, the deliberate multi-ready refusal pin
(`channels/select-multi-ready`, slice 4), and BUG-025's general-path
pin (`multi-assign/store-order-plain`, pre-existing machinery) — plus
311 negative cases, all green.

### Convergence-round response (2026-08-06, review of the delta-response commits)

The convergence verifier confirmed five findings — headline: the D3
per-target store-then-next fix had traded BUG-025's phase-2 collapse
for the OPPOSITE one (storing target k before target k+1's ADDRESS
evaluates: `i, bs[i] = <-ch` go 301/ours 304 with NO panic involved,
both statement and select forms). Per the round's structural directive
("no more patches trading divergence classes"), spec §Assignments' two
phases are now EXPLICIT machine structure, and every multi-target
store path rides it. Eleven red-first pins (all go-run-verified; three
land green as collapse-direction guards), five movements:

- **BUG-029 (critical), machine movement**: `tgtOpK` (phase 1)
  evaluates every target's OPERANDS left-to-right after the
  communication, resolving each target to a store-ready `TargetRef`
  (`targetPlan`/`completeTargetRef`: direct / index / field / mapElem)
  with the OUTER address operation's check DEFERRED; `storeK` (phase 2,
  `.next`-driven) stores ONE target per rule step, left-to-right,
  `storeTarget` firing the deferred nil/bounds/nil-map check at the
  store. CORRECTED at round 4 (BUG-033): the round-3 claim that this
  one-level boundary "is exactly gc's realized point" was FALSE for
  nested chains — `a[i].f` fires the inner index check in phase 1
  where gc defers the WHOLE address-former chain to the store. The
  now-probed boundary: every `indexAddr`/`fieldAddr` step of the
  target's spine is phase-2 (`targetSpine`/`resolveChain`), while
  VALUE operations in the base (an index-GET inner slice element, a
  deref) are index-expression operands and stay phase 1. Pinned from
  both directions: `nil-index-base-second` (phase-1 operand panic, go
  1000), `{field,oob}-second-target-stores-first` (phase-2 store-time
  checks, go 1150), `multi-assign/chain-field-over-index/*` (chain
  deferral, go 105) and its `inner-value-guard`/`array-nested` green
  contrasts. Relation/stepFn lockstep; positional case
  tags re-derived by compiler probe; no new Choices sites.
- **BUG-029 select half, frontend movement**: `machineSelectTargets`
  passes plain-lvalue clause targets straight into the clause head
  (the machine's step-4 delivery), replacing body-side single assigns
  whose address-then-store interleaving was the same collapse; falls
  back to the temp lowering exactly where step-4 clause-locality or
  machine expressiveness demands (`:=`, blanks, interface boxing,
  hoisting targets — unselected-lhs pins stay green).
- **BUG-030 (major)**: a TWO-target receive's map-element target rides
  the plan as `Assignee.mapElem` ("map" wire target) — its store is a
  phase-2 step and survives a later target's panic
  (`recv-map-elem/first-store-lands`, go 1050). Single-target
  `m[k] = <-ch` keeps the post-statement map-assign (one store; carries
  the boxing wrap); interface-valued maps in the two-target form fail
  closed. BUG-025's false "receive instance IS fixed" prose corrected.
- **BUG-025 CLOSED (the "open half"), machine movement**: the check
  "does the phase-split machinery naturally fix the general path"
  came back YES — `assignMany` left `stmtPlan`/`applyStmtOp` entirely
  and enters the same `tgtOpK` phase with its RHS expressions carried
  through; the new `rhsK` frame evaluates them left-to-right after the
  targets, then `storeK` stores per step. `StmtOp.assignMany` and
  `locsOf` removed outright (no inert dead arms). Pins flip:
  `store-order-plain` (the spec's own `x[1], x[3] = 4, 5`) and the new
  `field-nil-store-time` (a plain assign's nil FIELD check is
  store-time — probed: go 1150). All twelve other multi-assign
  order/aliasing pins stay green.
- **BUG-032 (minor)**: the fnHasRecv `len`/`cap` hoist's justifying
  claim ("over-hoisting is unobservable") was FALSE for the OPERAND —
  hoisting drags its panic ahead of spec-unordered panics to its left
  (a DEAD receive elsewhere in the function changed which panic
  fired). Choice argued: restricting the hoist to syntactically
  PANIC-FREE operands (`panicFreeOperand`: identifiers, literals,
  pointer-free selector chains) and FAILING CLOSED on the rest beats
  both alternatives — inline silently loses the len-vs-receive order
  (BUG-023 returns), and full-statement ANF linearization (hoisting
  every panicking operand of receive-bearing statements) is a large
  emitter rework deferred until a real target needs the shape. The
  discriminator pin `recv-order/dead-recv-len-operand` becomes a
  PERMANENT fail-closed refusal (differential → frontend-export), like
  `select-multi-ready`; the false claims in wire.go and
  BUG-023/BUG-026 are corrected in place.
- **BUG-031 (minor, pre-existing)**: `deferNoopEmitted` now
  saves/restores with each declaration/stencil emission, so the
  `$deferRecoverNoop` registration rolls back WITH `e.lifted` on both
  quarantine paths (`defer/recover-noop-after-quarantine` flips
  green).
- **NOTE finding**: `emitChanRecvAssign`'s stale pre-bind docstring
  (describing the behavior BUG-028 deleted) rewritten with the fix.

Convergence-tip counts: 1080 exec cases, 1000 pass / 80 fail — the 78
pre-existing non-channel gaps, the deliberate multi-ready refusal, the
BUG-032 fail-closed refusal marker, and zero open convergence
findings — plus 311 negative cases, all green. check-bugs green
(BUG-025/029/030/031/032 all fixed-with-green-pins or
refusal-reclassified; untriaged ledger unchanged at 16).
