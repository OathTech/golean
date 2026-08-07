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

### Round-4 convergence-check response (2026-08-06)

The round-4 verification confirmed the phase-split SHAPE (contrast
matrix green on every migrated form; all 11 round-3 pins replayed
green) but found the MIGRATION incomplete and two closure claims
overclaimed — with every headline divergence verified PRE-EXISTING
(base behaves identically; the round-3 diff narrowed the class while
the prose said "every multi-target store path"). Nine confirmed
findings, zero refuted; 22 red-first pins (18 red, 4 boundary guards);
five movements:

- **BUG-033 (critical): the address CHAIN.** `targetPlan` deferred
  only the outermost address op — `a[i].f` fired the inner index
  check in phase 1 (go 105 / ours 100, all three migrated paths). Now
  `targetSpine` decomposes the full `indexAddr`/`fieldAddr` spine
  (anchor + index operands = phase 1) and `resolveChain` replays it at
  the store. The probed boundary: a VALUE step in the base (index-GET
  inner slice element `aa[9][0]` on `[][]int`, a deref) is an operand,
  phase 1 — pinned green from both directions (`inner-value-guard`,
  `array-nested`). The round-3 ":exact gc point" claim is corrected in
  place above.
- **BUG-037 + BUG-034: built, validated, and honestly REVERTED.** The
  spine migration for single `.assign` (`assignFirst`) and the
  comma-ok forms (`RhsOp`/`applyRhsOp`) was implemented and flipped
  all five pins with zero corpus drift — and then reverted inside the
  round: retiring `assignTargetK`/`assignStoreK` and
  `StmtOp.mapLookup`/`.typeAssertStmt` breaks the shipped WP law
  families built on them (`wp_assign_start`/`wp_assign_store*` with
  the `wp_assign_lit` witness; `wp_map_lookup`, used by the HEADLINE
  quorum walk). Restating those laws over the spine is a coordinated
  machine+laws slice — scheduled together with BUG-025's call
  write-back (one retirement, one law rework, three consumers), per
  the round's own migrate-or-scope-honestly standard. The five pins
  stay red.
- **BUG-035 + BUG-036: the lowerings that bypassed the spine.**
  Blank-containing multi-assigns become ONE `.assignMany` with typed
  discard locals (decoder); the select temp-fallback's write-back
  becomes ONE body-side multi-assign (emitter) — clause locality
  unchanged, both targets' hoists before both stores.
- **BUG-038 + BUG-039 (minors):** `indexTargetLoc` gains the `.nil`
  panic arm (nil pointer-to-array store was wrongly stuck);
  `panicFreeOperand` consults `Selections[…].Indirect()` (the
  embedded-pointer fail-open hole — the discriminator becomes a
  permanent fail-closed refusal like dead-recv-len-operand). BUG-032's
  entry carries both amendments plus the assignment-path
  unordered-envelope note (spec-legal, pre-existing, recorded).
- **BUG-025 REOPENED (the honest disposition for the call write-back).**
  Its own scope line always named frame-exit `storeMany`: the
  multi-value CALL path still resolves target checks BEFORE the call
  (suppressing the call and its effects — go 117/ours 100), loses the
  call's own panic to our target check, and stores all-or-nothing.
  Migrating it means carrying `TargetRef`s through `Cont.frame` (the
  most-threaded frame: defers, panic paths, recover walk) and routing
  frame exit through `storeK` — deliberately scoped to the NEXT
  machine slice rather than rushed into this round; three pins
  (`multi-assign/call-write-back/*`) keep it red and visible, and the
  spine machinery (TargetRef/storeK/targetsPlan) is call-path-agnostic
  and ready for it.

Round-4-tip counts: 1102 exec cases, 1013 pass / 89 fail — the 78
pre-existing non-channel gaps, the three deliberate refusal markers
(select-multi-ready, dead-recv-len-operand, dead-recv-len-embedded),
BUG-025's three call-write-back pins, and the five BUG-034/BUG-037
pins held open by the coordinated-laws-slice disposition — plus 311
negative, all green. check-bugs green (39 bugs; untriaged ledger
unchanged at 16 — the READ-position pointers/nil-array-index-panic
stays there: a different, index-GET path).

## Slice-2 build log (2026-08-07, branch `channels-arc-s2`)

Executed as decided (goroutines + ThreadPool, D1/D2a/D5-scope/D6/D8).
Guardrails first: 38 red-pinned `goroutines/` cases (all go-run
verified) BEFORE any machinery. Decisions and findings DURING the
build, recorded here:

- **PROBE FINDING — `go` of a nil func value is a runtime FATAL at the
  SPAWN, in the SPAWNER** (`fatal error: go of nil func value`, exit 2;
  runtime `newproc`), REFUTING the machine-shape note §6's analysis
  ("nil-callee panics at invocation in the CHILD, the deferCall rule").
  The fatal class (non-panic, non-deadlock abort) is unmodeled; the
  spawn step refuses fail-closed (`.unsupported`) and
  `goroutines/spawn-edge/nil-func-fatal` is a permanent red pin until a
  fatal class exists. Guardrails-first caught this before the machinery
  encoded the wrong rule.
- **MultiConfig shape**: `{threads : Array Config, shared : ExecState,
  cur : Nat}` — APPEND-ONLY pool: a spawn pushes, a finished goroutine
  keeps its terminal config as a tombstone (never runnable again), so
  the ARRAY INDEX is the stable goroutine id for its whole life (D1's
  stable-identity requirement with no separate id carrier; main = 0).
  `cur` is the running goroutine; "goroutine exit" needs no explicit
  step — the finished cur is at a boundary and unrunnable, so the next
  pool step reschedules.
- **The scheduler (L1, first live Choices site)**: context switches
  ONLY at registry boundaries (`Config.atBoundary`: chan/select apply
  positions, the no-operand select entry, spawn positions, terminals,
  parked shapes); the pick is consumed ONLY at `|runnable| > 1`
  (envelope statement at `runnableIdxs`: the spec has NO scheduling
  text — "any runnable goroutine"; width = `|runnable|`). Scheduling
  folds into the same `stepMulti` call as the picked goroutine's step,
  so fuel counts exactly one goroutine-step per pool step — which is
  what makes the conservation theorem an `Except.map` away from
  `stepFn`.
- **Pairing = ARRIVAL INTERCEPT; wake = CELL-BASED** (D7 realized).
  AS FIRST SHIPPED the intercept fired only when the op would BLOCK —
  the S2 audit's headline major: buffered ops bypassed parked waiters
  (gc dequeues `recvq` BEFORE testing buffer room), gc's handoff
  observation (len 0 beside a parked receiver) was UNREACHABLE on
  every stream (too-narrow, the theorem-transfer-breaking direction),
  and this bullet's original invariant claim was FALSE for buffered
  channels. REDESIGNED at the audit response: every channel/select op
  at its apply position consults PARKED PARTNERS FIRST (`arrivalPlan`
  — gc's waiter-queue priority): matched sends hand off directly
  (never buffer beside a parked receiver — breach asserts
  `.internal`), matched receives take the buffer HEAD and REFILL from
  the parked sender in the same step (gc's `recv()` same-slot
  semantics — len preserved), and select readiness is waiter-EXTENDED
  (the audit's second major: a select with `default` now sees parked
  partners, both clause directions). With that priority the
  hchan-invariant analogue chan.go L17-18 is RESTORED AND RE-ARGUED
  (`Multi.lean` file docstring): parked receiver ⇒ empty buffer,
  parked sender ⇒ full buffer, hence matched parked-parked pairs
  cannot coexist on any capacity; AND every arrival — send, recv, and
  (since the convergence round) each SELECT clause — checks CLOSED
  before pairing, so no arrival pairs across a close and a `close`
  can never steal an already-pairable rendezvous in either direction.
  Discriminating pins: four stream-pinned
  pool eval-tests (verified RED on the pre-fix machine with the
  predicted divergent values 110/5091/99/99, green after) + the two
  membership envelope pins in `sched-dependent/` (go-run oracle:
  handoff/communication are gc's DOMINANT outcomes, 199970/200000 for
  the select shape); a strict-lane corpus case cannot observe buffer
  occupancy confluently, which is why the green lanes were
  structurally blind here.
- **FIFO through pressure**: a direct handoff happens only against an
  empty buffer (implied by the restored invariant); a receive meeting
  a parked sender over a nonempty buffer gets the HEAD, the sender's
  value entering at the tail (probe p18's same-slot trick). The L4
  waiter-pick site (envelope statement at
  `chanArrivalPlan`/`selectArrivalPlan`: no spec text on waiter order
  — "any matching waiter", gc's FIFO wakeup is a membership point;
  width = #matches, clauses counted individually) consumes only at
  width > 1. Both envelope statements carry width metadata for the
  slice-4 enumerator.
- **Select wake IS in scope** (the charter's "waking slice-1's blocked
  configs" includes `.blockedSelect`): parked selects pair op×select in
  both directions and wake via `readyClauses`/`commitClause`. FAIL
  CLOSED (visible `.unsupported`, never silent): multi-ready at wake or
  arrival (the L2 envelope, slice 4), select-with-select rendezvous
  (both sides parked selects — unmodeled this slice; pinned only by
  review, no corpus case constructs it deterministically).
- **D6**: main's terminal ends the program with main's outcome (the
  shared state at that instant is the joined final state); an
  unrecovered panic in ANY goroutine aborts the program with its
  message. Deadlock = no runnable goroutine, classified BEFORE the fuel
  check exactly like `execStmtLoop`'s terminals.
- **Driver**: `runProgramPoolM` = `runProgramSetupM` (factored out of
  `runProgramM` — shared wiring, no drift) + `execProgLoop`; the CLI's
  `native-json-run` subject phase now runs on the pool. `$pkginit`
  stays sequential — `go` during init refuses via `stepFn`'s
  fail-closed spawn position (red pin `spawn-in-init`).
- **THE CONSERVATION THEOREM** (`execProg_single_eq_execStmt`,
  `MultiSound.lean`): proof shape as predicted near-definitional —
  `stepMulti_single` shows the one-thread pool step IS `stepFn` up to
  an `Except.map` (single runnable ⇒ no scheduler consumption; no
  partner ⇒ the intercept is inert — `pairCandidates` scans waiters
  FIRST so a partnerless park never touches the cell, keeping the
  equation literal), lifted by a fuel induction to: every sequential
  result in the TRANSFERABLE classes (`.ok` at any terminal,
  `.fuelOut`, `.panic`) is the pool result verbatim — outcome, state,
  stream, and fuel accounting all equal. Deliberately excluded classes,
  recorded in `transferable`'s docstring: `.deadlock` (an ARTIFICIAL
  wake-ready blocked seed would resume in the pool; sequential runs
  never produce one — the corpus's 12 deadlock cases validate the
  deadlock direction empirically instead) and the fail-closed
  diagnostics (spawn positions refuse sequentially, fork on the pool).
  Verified BOTH ways per the charter: the theorem + the full corpus
  bit-identical (ZERO drift on all 1102 prior ids under the pool
  driver).
- **Correspondence kit**: `StepE` (the per-goroutine `Step` SPAWN
  COMPONENT — every `Step` lifts with `[]`, spawn positions fork one
  child; the iris-lean `Language` shape for slice 5) + the pool
  relation `StepM` (thread/park/pair/wake; deadlock relation-silent,
  mirroring the sequential blocked configs). `stepMulti_sound` and
  `stepM_complete` both shipped, both constructive
  (propext+Quot.sound), axiom-pinned in Audit. Completeness routes the
  L4 alignment through `stepFn_oblivious` via a new 190-rule sweep
  (`step_blocked_shape`: a step INTO a blocked config never starts
  from a stream-consuming shape).
- **D8 statement notions**: `GoTripleC`/`ProgressExecC`/`GoSpecC` over
  the `execProg` carrier (pre = single-threaded `InitialSplit`, post =
  joined final state `.normal`-pinned — main's `.normal` IS
  "mainNormal" — one stream for schedules + latitude; `ProgressExecC`
  excludes the same error classes as the sequential `ProgressExec` —
  which already forbids `.deadlock` since slice 1 — but on the POOL
  carrier, i.e. on every modeled schedule: a proven concurrent spec
  implies deadlock-freedom on every schedule; wording corrected at
  the S2 audit response). WITNESS STATUS, per the
  non-vacuity gate: the full `GoSpecC` instance is the SLICE-5
  deliverable (this note's own slice plan: "the GoSpecC witness
  proved") — discharging `∀ ch` needs the concurrent WP or a
  pool-level `allStreamsOk` analogue, neither slice-2 scope. Slice 2
  ships KERNEL witnesses instead (`Specs/GoldenForkJoin.lean`): the
  fork/join rendezvous under three pinned streams realizing three
  DISTINCT schedules (main-first / worker-then-main / worker-twice —
  the S2 audit caught the original third stream aliasing the second
  mod the scheduler bound; the stream is now all-ones, distinctness
  argued in the witness file) all completing `.normal` with the 42
  readout, plus the all-asleep two-goroutine program classifying
  `.deadlock` under two streams.
  The `GoSpecC` definitions are marked scaffolds in their docstrings.
- **DESIGNATED-STATEMENT-SET CHANGE**: the five fork/join kernel
  witnesses join the statement-TCB gate (33 → 38; closures verified
  Iris-free and relation-free); `StepE`/`StepM` join the gate's
  forbidden relation set; Challenge/Solution/judge-config extended in
  sync. **THE COMPARATOR LANDMARK IS OWED AT ARC END** (landmark
  cadence — deliberately not run in this slice, never part of ci).
- **Frontend fail-open fixed** (found by the guardrails): a bare
  builtin STATEMENT (`recover()` as a deferred closure's statement)
  emitted an undecodable node that took the WHOLE package down; it now
  quarantines per-decl with a precise reason. The bare-recover
  statement LOWERING itself is a recorded gap (red pin
  `spawn-edge/child-recovers`; the value-position form is unaffected
  and green throughout `close-wake/`).

OWED (recorded, not silently dropped): the Comparator landmark at arc
end; the slice-5 `GoSpecC` witness + pool ∀-streams checker; `MultiWf`
PRESERVATION (the foreign-thread `ConfigWf` frame needs a step-level
`nextAddr` monotonicity lemma the sequential kit does not expose —
`MultiWf` ships as a marked scaffold, the declared invariant carrier
for slice 3's detector); the D5 fairness-scope precision note (the
∀-stream `Terminates` claim for the blocking-discipline class — to be
made precise when a concurrent `Terminates` is first stated, slice 5);
the fatal error class (go-of-nil-func); bare-recover-statement
lowering; select-with-select rendezvous.

Slice-2-tip counts: 1140 exec cases, 1047 pass / 93 fail — the 89
slice-1-tip fails carried unchanged (zero drift on every prior id)
plus the 4 deliberate goroutines reds (sched-dependent/first-come —
slice 4's schedule enumerator; spawn-edge/nil-func-fatal — the fatal
class; spawn-edge/child-recovers — bare-recover lowering;
spawn-in-init — init stays sequential this slice); 311 negative, all
green; 87 machine eval-tests green (82 → 87, the 5 new pool pins:
rendezvous, multi-goroutine deadlock, D6 main-exit, close-wake,
nil-spawn refusal); check-bugs green (untriaged 16 → 18, both pins
recorded); baseline re-pinned in the frontend commit with the zero-
drift statement.

### S2 audit response (2026-08-07, pre-merge audit of this slice)

Nine confirmed findings (one refuted), all addressed on the branch —
pins first, then the fix, then the claim/gate corrections:

- **MAJOR (semantics): buffered ops bypassed parked waiters.** Fixed
  by the waiter-queue-priority redesign recorded in the corrected D7
  bullet above (`arrivalPlan` replaces the blocked-outcome intercept;
  handoff/refill per gc's `chansend`/`recv`; invariant chan.go L17-18
  restored and the close-window argument re-verified against the NEW
  design). Machine movement with relation/interpreter lockstep: the
  `StepM` rules are now thread (partnerless — park merged in), pair
  (arrival pairing, no `stepFn` involvement), wake;
  `stepMulti_sound`/`stepM_complete`/`stepThread_single`/
  `arrivalPlan_singleton` reworked (the pairing completeness no
  longer needs `stepFn_oblivious`; `step_blocked_shape` deleted).
  Conservation theorem statement UNCHANGED; full corpus ZERO-drift on
  all 1140 prior ids under the new semantics.
- **MAJOR (metatheory): select-with-default blind to parked
  partners.** Same root, same fix (waiter-extended readiness incl.
  the default decision); the non-blocking-select idiom is
  north-star-relevant (raft's `node.Tick`). Both select directions
  eval-pinned; the handshake shape membership-pinned with the go
  distribution recorded.
- **MINOR: spawnStep's nil-interface claim.** Docstring corrected
  (pointer-box class → child; nil-interface class is SPAWNER-side and
  frontend-hoisted; the indistinguishable-classes hazard recorded);
  both classes corpus-pinned
  (`spawn-edge/{ptr-box-child-aborts,nil-interface-recovered}`).
- **MINOR: ProgressExecC "strictly larger exclusions"** — false
  (sequential `ProgressExec` already forbids `.deadlock`); docstring
  and this note corrected: the delta is the CARRIER (every schedule),
  not the exclusion set.
- **MINOR: duplicated baseline row.** Clean re-pin removed it;
  `coverage-baseline-diff` now FAILS on duplicate baseline ids (the
  latent last-wins laundering hole closed).
- **MINOR: the third fork/join witness aliased the second** (equal
  pick sequences mod the scheduler bound 2). The alternating stream
  is now all-ones — worker-parks-first, the handoff's OTHER direction
  — with the distinctness argument in the witness file;
  Challenge/Solution/judge-config synced (the other 37 designated
  statements byte-identical; the Comparator landmark already owed at
  arc end replays the corrected set).
- **NOTES:** `transferable`'s `.deadlock` justification now names
  which theorem needs it (the loop lemma; the headline's exec seeds
  never block — a strengthening opportunity recorded, deadlock
  preservation validated by the 12 pinned cases); `execProg`/Surface
  prose citations matched to the theorem's actual strength (the
  diagnostic classes are covered by the bit-identity check, not the
  theorem); the C-family scaffold trio got Audit deletion anchors
  like its sequential twins; the stale two-modules ci comment (the
  refuted finding's residual) fixed.

Post-response counts: 1145 exec cases, 1050 pass / 95 fail (the 93
carried + `sched-dependent/{select-default-handshake,len-handoff}`,
the two audit-major envelope membership pins for slice 4; three new
ids PASS); 311 negative green; 92 eval-tests green (87 → 92: the four
waiter-priority discriminators — red-verified pre-fix at 110/5091/99/
99 — plus the no-partner default-member guard); check-bugs green
(untriaged 18 → 20, both pins recorded); baseline re-pinned from the
full run in the fix commit.

### S2 convergence-round response (2026-08-07, review of the audit-response commits)

Two confirmed findings (none refuted); the headline is a CRITICAL
introduced BY the audit-response rework itself:

- **CRITICAL: `selectArrivalPlan` had no closed-channel guard.**
  `chanArrivalPlan` refused to pair on closed in both directions
  (matching gc's closed-before-dequeue), but the select path computed
  its waiter lists unconditionally — and `clauseReady` counts closed
  as ready in both directions — so an ARRIVING select paired with a
  parked partner on an already-closed channel: the send clause
  completed normally where Go panics 200000/200000 (a guaranteed
  panic silently erased — too-wide, no oracle), and the recv clause
  took the parked sender's value ok=true while Go close-wakes that
  sender into its panic. Unreachable at 5cee9a1 (the old
  blocked-outcome intercept never ran for cell-ready selects) —
  introduced by moving the intercept in front of `stepFn`. FIXED by
  the per-clause closed guard mirroring `chanArrivalPlan`'s (the
  closed clause stays cell-ready and falls to `applySelect`'s correct
  semantics); the close-window docstring/design claims are RE-RECORDED
  against the arriving-select case (invariant clause (iv): no arrival
  pairs across a close). Pins: two stream-pinned eval discriminators,
  red-verified pre-fix at exactly the buggy values (103 where go
  guarantees the panic; 7100 where go gives 5) and green after; plus
  the `select-closed-arrival/{send,recv-parked-sender}` corpus pins
  (go-run verified: unconditional panic / stable 21) — confluent
  shapes that pass both sides on the strict lane's four streams (the
  discriminating schedule needs worker-parks-first-twice, which those
  streams never realize; the slice-4 enumerator will) and pin the
  oracle answers for it.
- **NOTE: `MultiSound.lean` trailing newline** restored (the tip was
  the repo's only .lean file without one).

Post-convergence counts: 1147 exec cases, 1052 pass / 95 fail (the
two new closed-arrival pins PASS; the fail set unchanged); 311
negative green; 94 eval-tests green (92 → 94); check-bugs green
(untriaged unchanged at 20); baseline re-pinned from the full run in
the same commit; the 38 designated statements byte-identical.

## Slice-3 build log (2026-08-07, branch `channels-arc-s3`)

Executed as decided (D2+D3's SECOND duty: segment-HB race detection,
racy-negative lane, litmus pairs, the NPDRF obligation's statement
layer). Guardrails first: all 13 `race/` corpus cases written and
`go run -race`-verified (racy shapes red at exit 66, green shapes
clean) BEFORE any machine change. Decisions and findings DURING the
build, recorded here:

- **Detector state is EXTERNAL instrumentation (the `Choices`/fuel
  mold), not a `MultiConfig` field** — a recorded deviation from the
  method line "detection state enters MultiConfig/StateWf carriers".
  `RaceState` (per-goroutine vector clocks, per-`Loc` TSan/FastTrack
  shadow, per-channel clocks) is threaded by the DETECTING
  `execProgLoop` beside the pool, updated by `raceUpdate` after each
  `stepMulti` call; it observes steps and never influences them except
  by the terminal `raceDetected`. Why: (i) the 38 designated
  statements stay byte-identical (a `MultiConfig` field would have
  reshaped every pool literal and `StepM` conclusion); (ii)
  `stepMulti`/`StepM` and the whole S2 correspondence kit are
  UNTOUCHED — grow by extension; (iii) the detector is definitionally
  inert on one-goroutine pools (`raceUpdate`'s first branch), which
  keeps sequential conservation literal (`raceUpdate_single` is the
  one new lemma the conservation proof needed) and the sequential
  corpus at zero detector cost. Consequence for `MultiWf`: it gained
  NO new consumer this slice (see the disposition below).
- **The footprint is a curated per-shape table (`stepAccesses`,
  Race.lean), not autologging at the `loadLoc`/`storeLoc` chokepoint**
  — the slice's second recorded deviation, argued in Race.lean's
  module docstring: chokepoint autologging would record accesses gc
  never performs (bounds-check loads, whole-cell loads for address
  formation) and channel-cell traffic (synchronization, race-free by
  spec) — false positives against the `-race` oracle in both cases —
  and `loadLoc` is a pure reader with no state to carry a log
  (instrumenting it = growth by revision). The table's arms map to the
  loadLoc/storeLoc call-site inventory of the access-bearing step
  shapes, curated to Go's access semantics; completeness over
  access-bearing shapes is a LOCKSTEP obligation like the relation's
  (a new stepFn arm touching user memory must add its footprint arm
  AND its inventory row), with the racy-negative lane as the
  executable check. [CORRECTED at the S3 audit response — the original
  paragraph ASSERTED the inventory ("the arms are exactly the
  call-site inventory") without enumerating it, and the audit found
  two missing arms (the interface-dispatch frame-entry deref, the
  instrumented `len(m)` read) plus a too-narrow over-approximation
  record; the inventory is now ENUMERATED in Race.lean's module
  docstring (footprint arms / model-internal / synchronization / fresh
  allocation), and the recorded approximations are its O1 + U1–U3
  entries: O1 whole-cell value-path composite reads (narrowed through
  immediate fieldGet chains; BUG-041 pins the array remainder), U1
  map-range per-iteration reads unperformed (BUG-005's fourth
  symptom), U2 len/cap — channels exempt (probe p26) but `len(m)`
  RECORDED (the original "len/cap record nothing / invisible to
  -race" claim was probe-refuted for maps), U3 the channel OBJECT
  unmodeled (gc flags close-beside-parked-send through it).]
- **THE HB EDGE SET IS GC'S RACE INSTRUMENTATION, quoted against
  go_mem at the implementation sites** (Race.lean `ChanClocks` /
  `RaceState.spawn`; the structural-alignment decision of D2+D3):
  - buffered send/recv = RELEASE-ACQUIRE on buffer slot
    `count % max 1 cap` — slot reuse every `cap` ops IS "The kth
    receive on a channel with capacity C is synchronized before the
    k+Cth send from that channel completes", and the send slot-op's
    release half is "A send on a channel is synchronized before the
    completion of the corresponding receive from that channel";
  - unbuffered pairing = bidirectional `racesync` join (both go_mem
    unbuffered directions at once, incl. "A receive from an unbuffered
    channel is synchronized before the completion of the corresponding
    send on that channel"); buffered handoff/head-refill transit the
    slot clocks exactly as gc's `send()`/`recv()` pretend the value
    crossed the buffer;
  - close releases into `closeVC`; a closed-empty receive acquires it
    ("The closing of a channel is synchronized before a receive that
    returns a zero value because the channel is closed"); a
    close-WOKEN sender's panic gets NO edge — [CORRECTED at the S3
    audit response: the original parenthetical claimed gc-parity
    ("gc's woken chansend performs no raceacquire"); the premise is
    true but the closer installs the edge from ITS side
    (`closechan`'s release-all-writers loop `raceacquireg`s each
    parked sender, exactly as for receivers), so our no-edge choice
    is strictly STRONGER than TSan's realized HB. Refusal-set
    agreement holds for a different reason: gc flags every
    close-beside-parked-send via channel-OBJECT instrumentation we
    do not model (inventory U3)];
  - spawn copies the parent clock to the child and bumps the parent
    ("The go statement that starts a new goroutine is synchronized
    before the start of the goroutine's execution"); goroutine EXIT
    gets NO edge ("The exit of a goroutine is not guaranteed to be
    synchronized before any event in the program") — pinned by the
    exit-no-sync eval pins.
  Event classification is pool-observational (pre/post configs;
  `wokenPartner` recovers a pairing's partner as the unique
  blocked→unblocked index) — no re-running of the L4 pick, no stream
  consumption, deterministic given the stream.
- **Cost, honest**: sequential programs (pool never exceeds one
  goroutine) pay ONE `Nat` comparison per pool step — the full-corpus
  run's wall-clock is unchanged and the 1147 prior ids are
  bit-identical. Multi-goroutine programs pay, per private step, a
  footprint pattern-match plus one shadow-list scan per access
  (entries = distinct post-spawn `Loc` paths, one epoch pair per
  goroutine per kind), and per registry op a clock join over goroutine
  count; the heaviest multi-goroutine corpus case (worker-pool/sum)
  runs in ~25 ms wall including process start.
- **Validation**: 13 new corpus ids (`race/negative/*` 5 racy,
  `race/litmus/*` 3 green edge pins + 2 racy + sb-chan red, and
  `race/free/*` 2 granularity guards), every racy id refusing on the
  default AND all three adversarial streams with `-race` red (exit 66)
  as the justifying oracle, every green id strict-lane PASS on first
  machine run — zero granularity false positives. Full corpus 1160
  exec: 1064 pass / 96 fail = the 95 S2-tip fails carried unchanged
  (ZERO drift on all 1147 prior ids) + sb-chan; 311 negative green;
  99 eval tests green (5 new: write-write refusal under two streams,
  the two BUG-040 documentation pins, the rendezvous-HB green pin);
  check-bugs green (40 bugs; untriaged 20 → 21, sb-chan recorded).
  Baseline re-pinned from the full run with the -race oracle recorded
  in its header.
- **BUG-040 (open, found by reasoning — the audit dimension's
  "unexercised paths" class): no POST-SPAWN reschedule point.**
  `atBoundary` marks the PRE-fork spawn position, where the child does
  not exist, and the parent's post-fork `.next k` is not a boundary —
  so a child can NEVER preempt a sync-free parent segment, the
  child-first interleaving of the exit-no-sync shape is outside the L1
  envelope (too narrow, theorem-transfer-breaking direction), and the
  detector — complete only over accesses that execute on modeled
  paths — sees a value leaf on every stream there. Not patched in
  this slice DELIBERATELY: every fix shape adds a `Choices`
  consumption site at the post-fork decision, which shifts every
  pinned stream including the three pinned-stream fork/join DESIGNATED
  witnesses (statement restatement = the charter's stop condition) and
  reworks the `StepM` correspondence. Scheduled with the slice-4
  enumerator (which needs the same machinery to enumerate child-first
  paths at all). Recorded in BUGS.md, the doctrine note's lane
  caption, ProgressExecC's scope caveat, and NPDRF.lean's obstruction
  list; pinned by the two `GoCore race BUG-040 pin` eval tests.
- **The NPDRF obligation's deliverable** (`GoLean/GoCore/NPDRF.lean`):
  `StepMFine` (the full-interleaving pool relation — `StepM` with the
  boundary condition dropped), the PROVED easy half
  (`stepM_le_stepMFine` / `reachesM_le_fine`: registry-point
  reachability ⊆ fine reachability, via "done/blocked configs are
  boundaries, so a mid-segment running goroutine is runnable"),
  `RacyFine` (co-enabled-conflict over the SAME `stepAccesses`
  footprint the detector records — one access semantics for statement
  and tool), and `NPDRFReduction` — the reduction STATEMENT as a
  Prop-valued definition, scaffold-marked per the non-vacuity gate (no
  theorem claims it; Audit carries deletion anchors and the
  `StepMFine`/`StepsM`/`StepsMFine` relations joined the
  statement-closure forbidden set). The mover decomposition plan is in
  the module docstring with the obstructions found by probing while
  building: (1) allocating steps commute only up to address renaming
  (`nextAddr` is shared — the appendSlice SPILL class); (2) fresh-cell
  `Heap.set` insertion order permutes the assoc list (commutation is
  extensional, not structural); (3) BUG-040 blocks the
  detector-completeness half; (4) D6 main-exit discard makes the
  joined final state schedule-sensitive even race-free (leaked
  goroutines' private cells). One representative both-mover pair IS
  proved: `storeLoc_root_frame` (a store touches exactly its root
  cell) and `loadLoc_after_disjoint_store` (the read mover) — the
  CROSS-ROOT half of the commutation core for the non-allocating
  store class (appendSlice in-place, copySlice, clearSlice, sortSlice,
  storeMany) [qualifier added at the S3 audit response: the lemmas are
  gated on root-cell disjointness, so same-root disjoint PATHS —
  distinct elements/fields of one cell, which the detector rightly
  calls independent — need the unproved path-level frame lemmas of
  NPDRF obstruction 6], axiom-pinned in Audit (they inherit
  `Classical.choice` from the pre-existing `Heap.lookup_set_ne`).
- **MultiWf disposition: NOT discharged; why, precisely.** The missing
  piece is real — a step-level `σ.nextAddr ≤ σ'.nextAddr` for the
  foreign-thread `ConfigWf` frame — and a probe (an automated
  premise-free sweep over `applyStrictOp`) left 47 of the op-applier
  surface's 60 arms (47 `applyStrictOp` + 13 `applyStmtOpCore`)
  needing bespoke destructuring, i.e. the cost is comparable to the
  existing `*_wf` family (`applyStrictOp_wf` is ~540 lines,
  StateWf.lean:2776-3312) TIMES the helper surface. [Figures corrected
  at the S3 audit response — the first form said "~700 lines" (~30%
  high) and attributed the ~60 denominator to the sweep alone.] The right implementation, recorded for the follow-up:
  EXTEND the existing `*_wf` conclusions with the `≤` conjunct inside
  their existing case analyses (`applyStrictOp_wf`,
  `enterRecvTargets_wf` and `StmtOpPres` already expose it; the
  missing conjuncts are `applyChanOp_wf`, `applySelect_wf`,
  `commitClause_wf`, and the top-level `step_preserves_wf_loc`),
  rather than a parallel premise-free family. Deprioritized THIS slice
  because the externalized detector state gave `MultiWf` no new
  consumer — it remains the marked scaffold and the declared invariant
  carrier it was at S2.
- **What stays red for slice 4** (unchanged plus one):
  `channels/select-multi-ready` (L2), `goroutines/sched-dependent/*`
  (3), `race/litmus/sb-chan` (the DRF-SC boundary set
  {1,10,11}/¬00), `goroutines/spawn-edge/{nil-func-fatal,
  child-recovers}`, `goroutines/spawn-in-init/in-init`, and the
  BUG-034/037/025 held-open multi-assign pins. The slice-4 enumerator
  additionally owes: lane-d "every enumerated path refuses" at full
  strength, sb-chan's set certification, and the BUG-040 fix (the
  post-spawn decision point) with its designated-witness restatement
  under its own sign-off. The Comparator landmark stays OWED at arc
  end.

### S3 audit response (2026-08-07, pre-merge audit of this slice)

Eleven confirmed findings (one refuted — the empty-buffer rendezvous
fall-through, unreachable by the re-derived hchan invariant), all
addressed on the branch — guardrails first (6 new go-run-`-race`-
verified cases, red-verified on the pre-fix machine at exactly the
predicted classifications), then the fixes:

- **MAJOR 1 (fail-OPEN): the interface pointer-box dispatch read had
  no footprint arm.** `dynamicDispatch?`'s `needsDeref` branch reads
  the pointee at FRAME ENTRY (a *T box dispatching to a value-receiver
  method copies the receiver out), and `stepAccesses` had no
  frame-entry arm — a `-race`-red program ran to `ok` on every stream
  (verifier-probed; isolated from BUG-040 by controls). Fixed:
  `dispatchAccesses` (mirroring the dispatch branch-for-branch) wired
  into every frame-entry shape — callArgsK/callValCalleeK/callValArgsK
  last-operand arrivals, all three deferred-call drains, and the SPAWN
  entry (recorded under the child's id after the spawn edge, matching
  gc's attribution). The audit's mandated INVENTORY audit was
  performed: every semantic-core loadLoc/storeLoc call site is now
  enumerated and classified in Race.lean's module docstring (footprint
  arm / model-internal / synchronization / fresh allocation) — the
  lockstep obligation's evidence, replacing the asserted-and-false
  "exactly the inventory" sentence. Pin:
  `race/negative/iface-dispatch` (red pre-fix on all streams, green
  refusal after).
- **MAJOR 2 (fail-OPEN, record-level per the verifier): map-range
  per-iteration reads.** gc's live iteration reads the map at every
  `mapIterNext` (`-race`-instrumented); our snapshot range performs no
  such read, so a write landing mid-range runs to a silent value. The
  root cause is BUG-005's snapshot design (no `stepFn` arm exists for
  the missing accesses — the lockstep obligation is structurally blind
  here, now said so in Race.lean U1). Disposition per the verifier:
  RECORD, not code surgery — BUG-005 gains its fourth symptom
  paragraph (race invisibility) and the permanent red pin
  `race/negative/map-range-iter` (in its Cases); the live-iteration
  surgery must add the footprint arm in the same movement.
- **MAJOR 3 (false-positive scope): interior reads vs disjoint-field
  writes over-refused beyond the recorded scope, and the free lane
  guarded only write/write.** Fixed on both sides: (i) NARROWING —
  `fieldChainTarget` projects a whole-cell read through the immediate
  `fieldGet` chain in its continuation, applied to BOTH the `evalVar`
  and `.deref` arms (the original record named only evalVar; the
  `.deref` form is the dominant `p.field`-through-`*struct` idiom) —
  `race/free/{field-read-write,ptr-field-read-write}` land green;
  (ii) the REMAINING envelope recorded precisely as O1 + BUG-041
  (value-path array-element reads and non-fieldGet composite reads
  stay whole-cell), red-pinned by `race/free/array-read-write`
  (expected ok, `-race` green, machine refuses — the over-refusal is
  fail-closed but now visible and carried by a bug entry, never a
  hidden misclassification).
- **MINOR (gc-parity claim wrong at four sites): the close-woken
  sender.** gc's `closechan` DOES `raceacquireg` parked senders (the
  closer installs the edge; the woken `chansend` premise was true but
  irrelevant), so our no-edge choice is strictly STRONGER than TSan's
  realized HB, and refusal-set agreement holds via gc's channel-OBJECT
  instrumentation, which we do not model. All four sites corrected in
  place (Race.lean `ChanClocks`, Multi.lean `raceWakeEvent`, doctrine
  caption, this log's HB list); the unmodeled chan-object accesses
  recorded as inventory U3. Behavior deliberately unchanged (the
  stronger edge set refuses more, the fail-closed direction).
- **MINOR (footprint completeness vs `RacyFine`): `len(m)` IS
  instrumented.** The verifier's probe refuted Race.lean's "len is
  invisible to -race" claim for maps (go1.26.5 flags `len(m)` beside a
  map write) — the `lengthOf` MAP arm is now in the footprint (pin
  `race/negative/len-map`, red pre-fix), channels stay exempt (probe
  p26). NPDRF gains obstruction 5: sharing `stepAccesses` between
  detector and `RacyFine` cancels shared under-approximation for the
  step-(iv) coupling but buys nothing for EXTERNAL adequacy
  (`¬RacyFine` ⇏ go_mem-DRF while U1–U3 stand), and unrecorded reads
  are invisible to the mover route too.
- **MINOR (mover granularity)**: the proved movers are gated on
  root-cell disjointness while the detector calls same-root disjoint
  paths independent — the named multi-cell constructs' same-root peer
  pairs need unproved path-level frame lemmas. NPDRF obstruction 6
  added; the build-log sentence and the mover section's prose
  qualified (CROSS-ROOT half).
- **MINOR (`NPDRFReduction` refutable as written)**: obstruction 4's
  scenario (sync-free leaked goroutines; `.done` compares whole joined
  states; coarse keeps ≤ 1 thread mid-segment in a sync-free pool
  where fine does not) refutes the `↔`'s ⊆ direction on race-free
  programs. The statement stays in draft form DELIBERATELY (the
  weakening — main-readout or main-reachable-scoped post-state — is
  its own reviewed decision), but the marking now says REFUTABLE, not
  merely unproven, forbids citing it even as a proof target, and no
  longer advertises the mover plan as closing the current form.
- **NOTE (byte-identity ≠ meaning-invariance)**: recorded here — the
  five fork/join designated witnesses' PROPOSITIONS strengthened when
  `execProg` became the detecting loop (each now also asserts no race
  is detected on its pinned stream), and their statement closures grew
  by `raceUpdate`/Race.lean (statement-TCB growth under D8's
  readability-as-specification review; the detector can only REMOVE
  accepted outcomes, so a detector bug breaks the kernel witnesses at
  build time — fail loud, never a false readout).
- **NOTE (MultiWf stale marking)**: Multi.lean's docstring no longer
  promises slice-3 consumption; it records the externalization and
  points at the `*_wf`-extension discharge route.
- **NOTE (cost figures)**: corrected in place above (~540 lines, not
  ~700; the ~60 denominator is 47 `applyStrictOp` + 13
  `applyStmtOpCore` arms).
- **NOTE (history reconstructibility, recorded honestly)**: slice 3's
  corpus + harness + machine landed in ONE commit (47dd4f4), so the
  guardrails-first ORDER within the slice is asserted, not
  reconstructible from history (the `-race` verifications themselves
  re-run today; a corpus-only first commit was awkward because
  `expected_status: race` did not exist before the harness half — a
  corpus+harness-then-machine split was available and should be the
  S4 practice). The S3 baseline re-pin also landed in a follow-up
  commit (40adc68) rather than the coverage-moving commit — deviation
  from the same-commit convention; protective purpose satisfied (zero
  drift on all prior ids, reason in the header), and exactly one
  commit (47dd4f4) is not standalone gate-green. This response's
  re-pin is in the same commit as its corpus change.

Post-response counts: 1166 exec cases, 1068 pass / 98 fail — the 96
carried (zero drift) plus the two new permanent red pins
(`race/negative/map-range-iter` → BUG-005,
`race/free/array-read-write` → BUG-041); four new ids PASS
(iface-dispatch, len-map — refusals live; field-read-write,
ptr-field-read-write — narrowing green). 311 negative green; 99 eval
tests green; check-bugs green (41 bugs; the two new reds are in
BUG-005/BUG-041 Cases, untriaged ceiling unchanged at 21); baseline
re-pinned from the full run in this commit; the 38 designated
statements byte-identical.

### S3 convergence-check response (2026-08-07, review of the audit-response commit)

Four confirmed findings (none refuted); the headline is a false-
positive class the audit-response commit itself introduced. Seven new
go-run-`-race`-verified pins (4 racy red, 3 free green), red-first
(`race/free/promoted-ptr-box` verified refusing on every stream on the
pre-fix machine; the four racy shapes verified already-refusing — pins
of current correctness per the verifier's own probes):

- **MAJOR (new false positive): promoted VALUE-receiver dispatch
  through a *T box over-refused.** The dispatchAccesses arm recorded a
  WHOLE-pointee read for every needsDeref dispatch, but for a
  SYNTHESIZED PROMOTION WRAPPER gc's autogenerated `(*outer).M` loads
  only the EMBEDDED field — a concurrent write to a non-embedded outer
  field is `-race`-green and was refused deterministically (the
  verifier's p1/p2/p3 causal isolation; a mainstream embedding+
  interface idiom). Fixed by the coordinator's preference (a): when
  the dispatch target has `Func.wrapper`, the read is recorded at the
  wrapper's promotion HOP PATH, recovered from the wrapper's OWN
  synthesized body (`wrapperForwardArg` — a deliberately shallow
  two-level extractor matching exactly the synthesized
  block/seqn/forwarding-call shape — then `recvFieldChain` peeling the
  pure fieldGet chain over `$recv`); any unrecognized shape (embedded-
  POINTER hops whose mid-chain deref reads another cell; any
  non-synthesized body) FALLS BACK to the whole-pointee read —
  over-refusal, recorded in O1/BUG-041's envelope, never fail-open.
  Non-wrapper needsDeref dispatch keeps the whole-pointee read (gc
  really copies it — the control stays red). Pins:
  `race/free/promoted-ptr-box` (red→green, gc value 15 matched on
  every stream) with `race/negative/promoted-dispatch` (embedded-field
  race survives the narrowing) and `race/negative/iface-dispatch` (the
  non-promoted control, stays racy) from both directions.
- **MINOR (arm families unpinned)**: one corpus pin per frame-entry
  dispatch family, all `-race`-verified, machine-verified in both
  directions: `race/negative/method-value` (callValCalleeK — the
  *T→T deref happens at the CALL) with `race/free/method-value-order`
  (creation concurrent, call ordered — green), `race/negative/
  defer-dispatch` (the frame-drain arms), and `race/negative/
  spawn-dispatch` (child-id attribution: a parent-attributed read
  would be sequenced with the parent's post-spawn write and silently
  green) with `race/free/spawn-dispatch-free` (write-before-go,
  ordered by the spawn edge). The `returning`/`panicking` drain arms
  share `deferEntryAccesses` with the pinned `.next` drain; a
  panic-path-drain corpus pin is deferred with that lowering gap
  (bare-recover class) recorded at S2.
- **NOTE (inventory exhaustiveness)**: the len(ch)/cap(ch) load sites
  had no row and fit none of the four categories — a new
  READ-BUT-UNINSTRUMENTED category carries them (real loads whose gc
  counterpart `-race` does not instrument; basis probe p26), and the
  dispatch row now records the wrapper narrowing.
- **NOTE (stale Audit.lean anchor)**: the deletion-anchor comment
  still said "awaiting proof"; refreshed to the draft/refutable
  marking (comment only; no designated statement text touched).

Convergence-tip counts: 1173 exec cases, 1075 pass / 98 fail — the 96
carried (zero drift on all 1166 prior ids) plus the two standing
BUG-005/BUG-041 red pins; 7 new ids all PASS. 311 negative green; 99
eval tests green; check-bugs green (41 bugs; untriaged ceiling 21
unchanged); baseline re-pinned from the full run in this commit; the
38 designated statements byte-identical.

## Slice-4 build log (2026-08-07, branch `channels-arc-s4`)

Executed as decided (select multi-ready + wake-order membership +
confluent lane; enumerator over schedules; envelope statements live) —
PLUS the slice's owed items: BUG-040's fix (authorized as anticipated
by D8), sb-chan's set certification, full-strength lane d, and the
sched-dependent un-reds. Red-first: the three L2 multi-ready envelope
shapes (entry/wake/arrival) were corpus-pinned red with go-verified
sets BEFORE any machinery. Decisions and findings DURING the build:

- **BUG-040 FIXED — the post-spawn reschedule point is the new Config
  marker `.spawned k`**, a registry op at spawn completion (this
  slice's one authorized new consumption POINT beside L2): `spawnStep`
  leaves the parent on it, `Config.atBoundary` includes it, its only
  step is the pool-level strip to `.next k` (`stepThread`; new rule
  `StepM.spawned`, mirrored in `StepMFine`); `stepFn` fails closed
  `.internal` on it (pool-only, like the blocked shapes). The child
  can now preempt a sync-free parent segment; the exit-no-sync race
  class is DETECTABLE (eval pins flipped: race on child-first [1],
  value leaf on main-first [] — and the pool enumerator pins BOTH
  leaves, the mixed-leaf class no corpus race row can express).
  **The predicted designated-witness re-pin turned out to need NO
  literal changes**: all three pinned-stream fork/join witnesses
  survive byte-identical (every stream still completes `.normal`/42),
  but the SCHEDULES the literals realize shifted — re-derived by probe
  (`.tmp/probe_fj_streams.lean`) and the distinctness argument
  re-recorded in GoldenForkJoin.lean (canonical = parked-receiver
  direction; adversarial now realizes worker-parks/recv-arrives via
  picks 1,0,1; all-ones = worker-twice-then-strip). Challenge/
  Solution/judge-config needed no sync (statement text unchanged); the
  arc-end Comparator landmark certifies the set over the changed
  machine. Conservation gains the `spawnedCont c = none` side
  condition internally; theorem statements unchanged; full corpus
  ZERO-drift on all 1173 prior ids.
- **THE L2 SITE, LIVE** (D4's envelope statement ships at
  `applySelect`'s docstring): spec step 3's "uniform pseudo-random
  selection" weakened possibilistically to "any entry-ready case";
  pick bound = ready-clause count, consumed only at width > 1. NO
  RE-RANDOMIZATION ON THE BLOCKED PATH: a woken select head-commits
  the first wake-ready clause in clause order (`resumeThread`),
  consuming nothing — wake-order latitude is L1/L4's (every gc
  first-event commit is realized by the prompt-wake schedule; a later
  wake's head-commit is a spec-legal member). Eval discriminator:
  the both-closed wake commits the FIRST clause with trailing stream
  picks untouched (`wakeMultiProgram`, stream [0,0,1,1,1] → 2).
- **`applySelect` factored through the stream-free `applySelectCore`**
  (the `applyStmtOpCore` precedent): the multi-ready arm PRE-COMMITS
  every ready clause, so apply-SUCCESS is pick-independent by
  construction (the ∀-choices kit's discipline — the mapIterNext
  precedent; a fail-closed commit error fires on every stream, panics
  stay per-pick as `.inr` members). This is what keeps
  `step_complete_any_wf` (and `progressExec_of_progress` above it)
  total with NO new exclusions; `stepFn_oblivious` gains the
  `consumesSelect` exclusion and `allStreamsOk` fails closed at select
  applies (conservative, the appendSlice precedent); `step_det`'s
  `choiceFree` excludes the select apply position.
- **The arrival plan split into a PURE analysis + consuming wrapper**:
  `arrivalCases` (`.cellPath` / `.single bc cands` — always a pair,
  single-commit unrepresentable by type / `.multi os` — one outcome
  per waiter-extended-ready clause) is the relation's carrier;
  `arrivalPlan` draws the L2 pick at `.multi`. A picked cell-only
  clause commits at the POOL level (`ArrivalOutcome.commit` — its
  waiter-extended bound differs from `applySelect`'s cell bound);
  pure-cell multi-ready delegates to `applySelect` (equal bounds by
  construction, argued at the site). `StepM` gains
  `pickPair`/`pickCommit`; sound/complete reworked over the
  `arrivalPlan_of_*` bridge lemmas. `raceUpdate` gains the pre-step
  stream and REPLICATES the step's consumption (L1 iff |runnable| > 1
  at the boundary; then the same `arrivalCases`/`Choices.consume`; then
  the cell-path replay) to recover the committed clause — it observes
  the stream, deterministic given it, consumes nothing.
- **THE ENUMERATOR WENT STEPWISE WITH MACHINE-COMPUTED PER-SITE
  BOUNDS** (the big in-slice design decision; membership design note's
  slice-4 addendum is the record). The old whole-run frontier at one
  author width is INTRACTABLE at scheduler scale (probed:
  first-come at width 3 exceeded 5M runs before finishing its alias
  probes — uniform width wastes width/bound per bound-2 site and the
  per-leaf ladder multiplies by path length). The rebuilt engine
  (GoLean/CLI.lean): DFS over the pool with shared prefixes,
  `stepNeeds`/`stepNeedsSeq` — the CLI consumption ACCOUNTANT
  mirroring only the consumption decision points while REUSING
  `runnableIdxs`/`arrivalCases`/`applySelectCore`/`appendSpillWidth`
  for every bound (GoCore untouched — the membership note's deferred
  "mechanical bound certification", taken without the core hook its
  deferral worried about); the author width is now a mechanically
  checked CAP (F2a made exact); the alias ladder retargets the
  accountant (per-site root-replays through the REAL semantics at raw
  picks b/2b+1/4b+3; an escaping observation refutes the bound);
  work is counted in machine steps + probe runs, fail-loud caps
  carried over. Pinned: pool driver-agreement eval tests (L1+pairing,
  L1+L4, lane-d refusal, exit-no-sync both-leaves), the in-engine
  unconsumed-picks drift alarm, and the harness coupling check.
  Scale on the certified corpus sets: first-come {12,21} — 24,298
  leaves, depth 14, ~1.02M steps+probes, 3.2 s; sb-chan {1,10,11} —
  30,186 leaves, ~1.28M, 5.3 s; worker-pool/sum singleton — 59,601
  leaves, ~9.9M, ~65 s (the heaviest); handshake/len-handoff/
  wake-multi/arrival-multi all < 0.1 s.
- **Lanes wired** (coverage-manifest + diff-coverage + fixture
  extensions in test-lane-validation): `confluent` (certify |set|=1
  over all schedules, then the full strict pipeline; the singleton is
  also pinned against the driver's observation), `racy` (MANDATORY
  for every race-expectation row: every enumerated path refuses,
  replacing the per-stream approximation), membership `members=<n>`
  cardinality pins, and plain+`-race` DUAL SAMPLING for membership
  rows (the doctrine update; live finding: cap-zero's -race sample
  lands on cap 1 — inside the F2-widened envelope, a live validation
  of the widening; first-come exhibits BOTH members only under
  -race). 41 confluent reclassifications (S4 audit correction: first
  recorded as 36 here, in the baseline header, and — as "49 stage
  reclassifications" — in commit 88fa982's message; the true drift
  decomposition is 6 result flips + 54 stage moves = 41 confluent +
  13 racy = 60 ids); 3 recorded stay-strict ids
  whose trees exceed tractable caps (pipeline/{two-stage,
  buffered-stage} >60M steps / >400 s, worker-pool/shared-feed —
  DPOR is the recorded later-additive layer, D9(c)).
- **Un-red**: channels/select-multi-ready (strict, the slice-1 refusal
  pin) + the six schedule pins — sched-dependent/{first-come,
  select-default-handshake,len-handoff} ({12,21}/{7,99}/{100,110},
  members=2 each), race/litmus/sb-chan ({1,10,11}, members=3 — the
  DRF-SC boundary certified, 00 mechanically excluded),
  select-wake-multi ({1,2}), select-arrival-multi ({10,20}), and
  channels/select-multi-ready/observable ({101,210}). Untriaged
  ceiling 21 → 24 (red-first) → 22 (L2) → 16 (enumerator).

Slice-4-tip counts: 1176 exec cases, 1083 pass / 93 fail (the 89
round-4-tip non-channel gaps and held-open multi-assign pins carried;
the remaining channel-adjacent reds: spawn-edge/{nil-func-fatal,
child-recovers}, spawn-in-init/in-init, race/negative/map-range-iter
(BUG-005), race/free/array-read-write (BUG-041)); 311 negative green;
107 eval tests green (99 → 107: the 8 pool-enumerator/wake-commit
pins; the two BUG-040 pins flipped in place); proofs green, 38
designated statements byte-identical; check-bugs green (41 bugs;
untriaged 16). Baselines re-pinned per movement — with one recorded
DEVIATION (S4 audit): the red-first commit (f4117e2) landed its three
new red ids WITHOUT the same-commit baseline/untriaged re-pin; both
landed one commit later (9209f4e, whose re-pin reason names them), so
f4117e2 is not standalone gate-green under --diff (the S3 note's
history-reconstructibility class; the untriaged-count entry labeled
"red-first commit" was recorded in 9209f4e). Every other movement
re-pinned in its own commit with zero unexplained drift.

STILL OWED (slice 5+, unchanged unless noted): the Comparator landmark
at arc end; the GoSpecC witness + concurrent WP (slice 5); MultiWf
preservation (scaffold); the fatal class (go-of-nil-func);
bare-recover-statement lowering; select-with-select rendezvous;
BUG-005's live-iteration surgery (now also the race U1 fix);
BUG-041's path-precise value reads; DPOR for the three stay-strict
confluent candidates; the NPDRF obligation (BUG-040's obstruction 3 is
now discharged by the fix — the reduction statement's remaining
obstructions stand).

### S4 audit response (2026-08-07, pre-merge audit of this slice)

Ten confirmed findings (two refuted), all addressed on the branch;
severities as verified (2 minor + 8 note after verifier adjustments):

- **MINOR (gate honesty): the enumerator's "Coverage argument" header
  docstring still described the retired uniform-width engine** — four
  false claims ("[0, B) alphabet", "CANNOT read a site's bound",
  author-asserted width PRECONDITION, the +B/+2B+1/+4B+3 offset
  ladder) contradicting the accurate engine section in the same file.
  Rewritten to the shipped accountant engine with an explicit
  SUPERSEDED marker, and the `maxWidth`/`workCap` field docs updated
  (width = mechanically-checked cap; work unit = steps + probe runs).
- **NOTE → TAKEN AS A FIX: the accountant drift alarm was ONE-SIDED**
  (over-supplied picks failed loud; a MISSED consumption site was
  silent — `Choices.consume` defaults to 0 on an exhausted stream —
  and unprobed, since only discovered sites get ladder rungs; the
  verifier confirmed the accountant exhaustive TODAY, six consume
  sites each mirrored). Upgraded to the TWO-SIDED SENTINEL alarm:
  every explored step (pool AND init phases) runs sentinel-suffixed
  and must return the sentinel exactly — a missed site draws it, an
  over-count leaves extra picks beside it, both fail loud. The
  detection primitive is eval-pinned both ways (an L1 site draws the
  sentinel / a non-site leaves it; a broken-accountant injection is
  not expressible, so the primitive is the pin), and THE
  ACCOUNTANT-EXHAUSTIVENESS INVENTORY (six semantic-core consume
  sites → accountant arms) is recorded in CLI.lean's engine docstring
  as a standing lockstep obligation, Race.lean-inventory style.
- **NOTE: the retargeted alias ladder's "pure redundancy" claim was
  FALSE** — the prefix-only probe exhibits only the bumped branch's
  all-defaults leaf, and the audit DEMONSTRATED (schedLenHandoff node
  [1,1]) a hypothetical under-count whose escaping residue aliases
  under the empty suffix but diverges one non-default pick deeper —
  refutation power the old per-leaf suffix multiplicity carried.
  Claim corrected in the engine docstring, `probeSite`, and the
  membership addendum: the ladder is the heuristic MAGNITUDE
  cross-check; the systematic accountant checks are the sentinel
  alarm and the external driver-agreement/coupling pins.
- **MINOR (×2, same root): the confluent reclassification count was 41,
  recorded as 36** in the baseline re-pin header and the build log —
  and the recording commit's "6 + 49 = 60" is internally inconsistent
  by the same 5 (true decomposition: 6 result flips + 54 stage moves
  = 41 confluent + 13 racy). Both tracked records corrected in place
  with the commit-message discrepancy noted (history not rewritten);
  the racy count (13) and flip set (6) were verified correct.
- **NOTE: applySelectCore's `.inr` panic arm is UNREACHABLE today**
  (`commitClause` returns channel panics as `.panicking`
  CONFIGURATIONS, never `.error (.panic …)`), its docstring
  misattributed the panic flow, and the arm's `throw` would have
  DROPPED the consumed L2 pick if it ever went live (stepFn's panic
  handler returns the pre-consumption stream). Docstring corrected
  (panics ride `.inl`; `.inr` is the defensive mirror) and the arm
  now returns the `.panicking` configuration WITH the pick consumed
  — the latent desync is closed while the defensive totality stays.
- **NOTE: the red-first commit's baseline/untriaged re-pin landed one
  commit late** (f4117e2 carried only the corpus files; 9209f4e
  carried the re-pin with a back-reference) — the build log's
  "re-pinned per movement in the moving commits" sentence corrected
  to record the deviation (f4117e2 is not standalone gate-green under
  --diff), and the untriaged-count entry's label fixed.
- **NOTE: the alarm-direction doc gloss** — folded into the sentinel
  fix and the addendum correction above (the membership note's
  "exactly what an escaping probe exhibits" now scoped to discovered
  sites).
- **MINOR: the four new in-harness lane gates had no Part-B
  fixtures** (slice 3's precedent gives harness-side guards
  landing-time fixtures). Added B3/B4/B5 to test-lane-validation's
  Part B: the members= pin refuses members=99 on a 2-member set; the
  confluent lane refuses a non-singleton observable; the racy lane
  fails loud on a mechanically-refuted width (width=1 under a bound-2
  site). All run under ci --diff.
- **NOTE: StepMFine's docstring said "four rule classes"** (bumped at
  BUG-040's +1 but not at L2's +2); corrected to six, matching
  StepM's.

Refuted (no action): the baseline-header flip-set/completeness claim;
the L2-pick-not-popped-on-panic claim (the pick IS consumed before the
old throw — the latent issue was the STREAM the stepFn handler
returned, fixed above as part of the `.inr` correction).
