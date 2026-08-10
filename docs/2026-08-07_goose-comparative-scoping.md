# Goose/Perennial comparative audit — scoping note (2026-08-07)

(Committed to docs/ 2026-08-07, verbatim from the worktree deliverable
recorded below — this provenance paragraph is the only addition. The
Part-C standing matrix it proposes is seeded in the same change as
docs/goose-perennial-comparison.md.)

Research worker deliverable. Written to the WORKTREE `.tmp`
(`.claude/worktrees/agent-a4e1479084141a9b5/.tmp/goose-comparative-scoping.md`)
— the main-repo `.tmp` path was refused by the worktree-isolation guard, so
this is the charter's stated fallback. Format: **[FACT]** cited
`file:line@rev`, **[ANALYSIS]** marked reasoning, **[PROPOSAL]** actionable
scoping.

CHARTER (user direction, verbatim intent): "a comparative audit against
Goose/Perennial's channels support — ideally we cover their capabilities and
more, but cleanly and precisely identify discrepancies. Identify THEIR test
examples over ALL features (not just channels) and show we can verify them
all." This note scopes that program into (A) a channels discrepancy matrix,
(B) their full test-example inventory assessed against GoLean today with a
phased import plan, and (C) a standing comparative-audit mechanism.

Revisions (recorded per charter; all their-side cites below are at these):

- `deps/goose` @ `3be88bbb4982f58e5813b6f0344302d5582c8e8a` (branch `new`;
  cited `@3be88bb`). Upstream development has moved into mit-pdos/perennial
  (goose README) — upstream drift check owed at each review (Part C).
- `deps/perennial` @ `43d4efabc22eb148eb239ebee89d1dd2ee54c900` (master;
  cited `@43d4efa`). The 2026-08-06 research note recorded upstream head 2
  dependabot commits ahead at that date.
- GoLean = main at the channels-arc merged state: baseline
  `baselines/native-full.tsv` header "recorded: 2026-08-07 commit:
  channels-arc-maint", 1193 exec cases (1099 pass / 94 fail), 311 negative;
  44 designated theorems (`proofs/Audit.lean`'s designated list + judge-config.json — count and citation corrected at the arc-final audit F14: this doc was drafted after the S5 response's 44th, goldenReturnsTwoC, and cited both a stale count and a stale line range); 167 concurrency-lane
  ids (channels/goroutines/race) — 160 PASS (99 strict, 41 confluent, 13
  racy, 7 membership), 7 FAIL (all recorded deliberate/held-open pins).

Evidence base: the six 2026-08-06 concurrency research notes (especially
`docs/2026-08-06_concurrency-research-goose-perennial.md`, same pinned revs),
the channels-arc design of record `docs/2026-08-06_channels-arc-design.md`
(slice 1-5 build logs + audit responses), and two fresh read-only enumeration
passes over `deps/goose` and `deps/perennial` performed for this note.

---

# PART A — Channels comparison matrix

## A.0 Architecture, one paragraph each

**[FACT] Their side.** Channels in Goose/Perennial are not machine
primitives: a generic Go library (`deps/goose/model/channel/channel.go`,
293 lines — 7-state offer machine `buffered|idle|sndPending|rcvPending|
sndCommit|rcvDone|closed` guarded by a `primitive.Mutex`, channel.go:7-29
@3be88bb) is goose-translated into GooseLang
(`perennial:new/code/github_com/mit_pdos/perennial/goose/model/channel.v`,
930 lines; the vendored Go source is byte-identical to goose's) and verified
once against HOCAP-style logically-atomic specs
(`new/golang/theory/chan/au_spec/chan_au_*.v`). The ONLY new machine syntax
is `SelectStmt` (`src/goose_lang/lang.v:216,248,283-289@43d4efa`), whose
step relation is assumed via the `go.ChanSemantics` typeclass
(`new/golang/defn/chan.v:72-115@43d4efa`). Blocking is spin loops
(`Send = for !TrySend(v,true) {}`, channel.go:105-113; nil ops `for {}`,
:108,192). The thread pool is Iris-standard: `Fork` appends to a list, no
scheduler, no fairness, no thread removal
(`src/program_logic/language.v:118-122@43d4efa`).

**[FACT] Our side.** Channels are primitive heap cells (`chanData`, D7) in
an executable, deterministic-given-stream interpreter that is both the
differentially validated model and the statement language; goroutines are an
append-only `MultiConfig` ThreadPool with stable ids; blocked goroutines are
blocked-`Config` shapes (no waiter queues in channel state); scheduling and
happens-before edges share one synchronization-op registry (D2+D3); race
detection is segment-HB vector clocks external to the pool; select is
entry-time operand evaluation + one readiness step + L2 choice among ready
(`docs/2026-08-06_channels-arc-design.md` D1-D9 and slice logs; modules
`GoLean/GoCore/{Multi,MultiSound,MultiStreams,MultiWfSound,Race,NPDRF}.lean`).
Validation is the six-lane differential taxonomy (D9) against `go run` /
`go run -race`, plus a schedule-tree enumerator certifying membership sets.

## A.1 Behavior-level parity (both sides model these, agreeing with gc)

[FACT unless noted; their cites from the fresh enumeration, ours from the
design note's slice logs + the corpus ids in parentheses.]

| Behavior | Theirs | Ours |
|---|---|---|
| Buffered FIFO, len/cap | channel.go:51-59,125-134,252-271@3be88bb | strict lane (channels/buffered-basic, builtins/make-channel-len-cap) |
| Unbuffered rendezvous | offer protocol channel.go:66-92,151-172 | pairing step, direct handoff (goroutines/rendezvous-hb) |
| close semantics: drain then zero/`ok=false` | channel.go:135-144 | channels/{closed-receive,range-closed}, close-edge/drain-zero-after-close |
| close panics: send-on-closed / close-of-closed / close-of-nil, gc's exact strings | channel.go:49-50,209-210,229-231; differentially pinned vs real chans channel_test.go:447-622@3be88bb | same strings as `runtimeErrorValue` payloads (slice-1 L9 narrowing); channels/{send-closed-panic,close-closed-panic,close-nil-panic} |
| nil channel: send/recv block forever; len/cap = 0 | channel.go:106-110,190-193,253,267 | nil ops → blocked config → deadlock terminal (channels/nil-values); len/cap 0 |
| select: send cases, recv cases (bare, `v = <-ch`, `v, ok := <-ch`, arbitrary lvalues), default, any arity, `select {}` | translation goose.go:1780-1893@3be88bb; semantics defn/chan.v:40-62,95-114@43d4efa; surface demo testdata/examples/unittest/chan.go:25-57 | SelectClauseHead machinery, entry-time operands, machineSelectTargets lvalue delivery (channels/select-*; scoping/select-clause-scope) |
| select entry-time operand evaluation, source order | `$ch_i`/`$v_i` lets, goose.go:1874-1889 (their own caveat "XXX: left-to-right evaluation, might not match Go", goose.go:1901) | selectOpsK, spec step 1 (channel-operands-eval-order pins; receive-vs-call lexical-order work, slice-1 log) |
| nonblocking ops never rendezvous with each other | no-offer asymmetry channel.go:90,173; pinned by Test2NBSelectNoProgress channel_test.go:1170-1207 | select-with-default sees parked partners but two defaults never pair (sched-dependent/select-default-handshake, membership-pinned {7,99}) |
| select on closed channels: recv ready with zero/false; send-clause commit panics | clause readiness incl. closed via the model | S2-convergence closed-arrival guard; goroutines/select-closed-arrival/{send,recv-parked-sender} |
| range-over-channel = receive-until-closed-and-drained | `Iter()` channel.go:274-292 + `chan.for_range` defn/chan.v:13-22 | decodeRange `"chan"` desugar (channels/range-closed, range-edge) |
| directional channel types | types.go:586-598@3be88bb | channels/{directional-types,make-directional,close-send-only} |
| `go f(args)`: callee+args evaluated in the spawner | goose.go:1654-1673 | spawn positions; spawn-edge pins |
| close during unbuffered handshake waits for the exchange | tryClose retry channel.go:203-219 | arrival-never-pairs-across-close invariant clause (iv), S2 convergence record |

[ANALYSIS] At the pure channel-behavior level we have reached coverage
parity-or-better with their model: every behavior their model implements is
a green corpus lane on our side, and both sides pin the same gc panic
strings. The differences are all in the surrounding machinery (A.2-A.4).

## A.2 They have, we lack

Classification key: **CAP** = capability gap (we should eventually close),
**DEL** = deliberate divergence (recorded decision, not a gap), **LAT** =
spec-latitude difference (both defensible; envelope shapes differ).

| # | What | Their evidence | Our status | Class |
|---|---|---|---|---|
| T1 | `sync` package: Mutex/RWMutex/WaitGroup/Once/sema specs proved over the goose-translated REAL stdlib source, atop a small trusted core (Mutex→CmpXchg spinlock, semaphore model; Cond notifyList STUBBED no-ops) | `new/trusted_code/sync.v:8-58@43d4efa`; `new/proof/sync.v` + `sync_proof/*` (9 files, ~35 wp lemmas) | Nothing. Recorded growth contract: a sync primitive is added by REGISTERING it (one scheduling point + one HB rule), design note D2+D3 | **CAP** — the top live blocker for their corpus (Part B) and raft-critical |
| T2 | `sync/atomic`: machine atomics (`LoadOp/AtomicSwap/AtomicAdd/CmpXchg`, lang.v:84-105,1372-1431@43d4efa) + 49 wp lemmas (`new/proof/sync/atomic.v`, their largest single proof file) | ibid. | Nothing; D5 records atomics as the `FairStream` prerequisite arc | **CAP** |
| T3 | Logically-atomic channel-op spec set: `send_au/recv_au/close_au` + nested AUs + two incomparable nonblocking variants; proved `wp_NewChannel/wp_Send/wp_Receive/wp_Close/wp_TrySend/wp_TryReceive/wp_Len/wp_Cap` | `chan_au_base.v:106-297@43d4efa` (canonical-weakest-spec problem documented at :244-263); `chan_au_{new,send,recv}.v` | ZERO channel WP/lifting laws — our concurrent Iris layer has only `wpC_fork`/`wpC_pure_det`/`wpC_spawned_strip` (`proofs/GoLeanProofs/LangC.lean`); channel facts export as operational history predicates / kernel certificates instead | **CAP** (deliberately deferred — slice-5 record: "no consumer this slice, no inert scaffolding"; lands with the decomposition arc) |
| T4 | Select WP specs: `wp_select_blocking` (`[∧ list]` per-case AUs), `wp_select_nonblocking`, `wp_select_nonblocking_alt` (∗-separated with not-ready witnesses → provable-unreachable default) | `theory/chan.v:272-299,427-455,584-619@43d4efa`; unreachable-default demo `wp_select_nb_guaranteed_ready`, channel_select_tricky_examples.v:117 | None (same deferral as T3) | **CAP** |
| T5 | Channel idiom spec libraries: bag, broadcast, contrib (Actris ghost theory), future, handshake, lock, mpmc (1022 ln), spsc (668 ln) | `theory/chan/idioms/*@43d4efa` (per-lemma list in the enumeration pass; entry idioms.v:1-9) | None. [ANALYSIS] their idiom set is a map of raft's channel patterns — broadcast/done-channel and bag are what `v3_proof/protocol.v` imports | **CAP** (successor-arc, after T3) |
| T6 | dsp/ — Actris dependent separation protocols over PAIRS of Go channels, with proofmode tactics (`wp_recv`/`wp_send`) and the COFE model in-tree | `theory/chan/idioms/dsp/{dsp,dsp_ghost_theory,proto_model,dsp_proofmode}.v@43d4efa`; example `wp_DSPExample` channel_dsp.v:35 | None (the "Actris-lite" layer named in D8 was deliberately not built in slice 5) | **CAP** (lowest urgency of the spec-layer family) |
| T7 | Frame-quantified WP proofs over genuinely-spawning programs (their entire proof portfolio is this) | e.g. `wp_simple_join` channel.v:259, all of A.5's examples | RECORDED SUCCESSOR DEBT: `goldenSpecC` is the sequential-degenerate lane; the spawning frame-quantified `GoSpecC` needs the pairing decomposition (pool `StepM` pairing touches two threads; iris-lean `Language` steps one) — slice-5 log + Surface.lean witness-status note | **CAP** (the named next-arc obstruction, sized) |
| T8 | Prophecy variables (HeapLang-inherited; used at scale in vMVCC) | lang.v:244-245@43d4efa | None; slice-5 log records "no prophecies needed — primitive channels make lifting laws the atomic specs" | **DEL** for channels; CAP only if a future target needs future-dependent linearization |
| T9 | Crash semantics + FFI worlds (disk, async_disk, filesys, grove network) and the storage-systems portfolio | lang.v FFI parameter; `testdata/examples/{append_log,wal,simpledb,...}` | Out of scope: our north star (etcd-io/raft, the library) needs no disk/net FFI | **DEL** (record; revisit only on a target change) |
| T10 | Translated Go stdlib surface: sync, atomic, time, strings, bytes, sort/slices (real stdlib pdqSort proved), context, fmt, encoding/binary, errors, io, log, math… | `etc/ci-goose-check.py:23-41@43d4efa` pins the source repos; `new/code/*`; ~60 stdlib wp lemmas + ~25 slices/sort | Our frontend refuses imports (`tools/nativefrontend/emit.go:4105,4148` — imported named types/methods fail closed) | **CAP** long-term; Part B quantifies which corpus files this blocks |
| T11 | North-star proof progress: in-progress etcd-raft + etcd verification (`wp_Node__Propose` Qed; etcd client 39 wp lemmas but 29 Admitted; readonly.v 955 ln, 5 Admitted) | `new/proof/go_etcd_io/raft/v3.v:17-29`, `v3_proof/*`, `etcd/client/*@43d4efa`; Go sources external: github.com/upamanyus/{etcd-raft,etcd} branch `goose` | Our quorum pilot is a raft fragment; no raft-package-scale work yet | **CAP** (this is the race; their surface is demonstrably WIP — 51 Admitted across new/proof's 376 wp lemmas) |
| T12 | Sub-step interleaving granularity + operational race-UB by construction (two-step na accesses, `naMode Reading n | Writing`; racy access → stuck) | lang.v:543-546,1352-1396@43d4efa | We rejected naMode (grows by revision, D2+D3); registry-granularity + the NPDRF reduction OBLIGATION, whose statement is currently a REFUTABLE-as-written draft (NPDRF.lean; S3 audit) | **DEL** with an honest open metatheory debt on our side — their granularity story is complete by construction; ours rests on the unproven reduction |

## A.3 We have, they lack

| # | What | Our evidence | Their status | Class |
|---|---|---|---|---|
| O1 | An executable semantics at all + `go run` differential validation (1193 exec + 311 negative cases, six-lane taxonomy, tracked baseline, zero-drift gates) | design note D9; `baselines/native-full.tsv` | Their GooseLang interpreter + semantics corpus was DELETED with the old semantics (perennial `eb748d43e`, 2026-01-30); the new semantics has NO interpreter and no differential harness (research note §5; `cmd/test_gen -coq` still references the absent `Perennial.goose_lang.interpreter`) | **DEL** on their part (casualty of the rewrite); our differentiator |
| O2 | Channel-model validation IN the trusted semantics: our interpreter IS the model under differential test. Their Go-model tests are real and good (spec-sentence-keyed `channel_spec_test.go:15-98@3be88bb`; runtime-derived + in-process model-vs-native differential `channel_test.go:210-310,447-622`; the `model/go_channel` native twin re-running the identical corpus) but validate the GO model — the model↔GooseLang correspondence and select-model↔`try_select`-axioms are TRUSTED, stated in their own header (select.go:3-5@3be88bb) | — | trust gap on their side | our structural advantage |
| O3 | Deadlock as an observable terminal matching gc ("all goroutines are asleep - deadlock!", exit 2), differentially tested (`expected_status: deadlock`) | slice-1/2 logs; channels/deadlock, goroutines/deadlock | Impossible: blocked = spin loops; a deadlocked program just diverges. No counterpart of Go's runtime detector | **CAP** on their side |
| O4 | In-machine race DETECTION: segment-HB vector clocks (TSan/FastTrack skeleton), HB edges quoted against go_mem at implementation sites, `raceDetected` terminal, racy lane "every enumerated path refuses" + `go run -race` (exit 66) as justifying oracle; DRF-SC boundary pinned executably (sb-chan {1,10,11}, 00 mechanically excluded) | slice-3/4 logs; `GoLean/GoCore/Race.lean` inventory | naMode makes races UB/stuck for PROOFS but is untestable — "Goose has no way to test its race semantics at all" (research note §4); no -race oracle use anywhere | **CAP** on their side |
| O5 | Recoverable channel panics: send-on-closed/close-of-closed/close-of-nil/make-negative are real Go panics — `recover()` works, messages differentially compared | channels/close-edge/recover-* (all green) | In the logic these are `False` branches in `send_au`/`close_au` (chan_au_base.v:205,295@43d4efa) — verified code must prove them impossible; `go.panic` has no proof rules found; the Go-model panics are unreachable-by-obligation. Go defines these as catchable panics | **DEL** on their side (proof-obligation style); faithfulness + testability win on ours |
| O6 | Select multi-ready with a CERTIFIED possibilistic record: L2 envelope statement at the site, membership lane with machine-enumerated observation sets + `members=n` cardinality pins, plain AND -race dual go-run sampling | slice-4 log; channels/select-multi-ready/observable {101,210}, select-wake-multi {1,2}, select-arrival-multi {10,20} | Nondeterminism exists (demonic permutation) but is unexplored: no schedule enumeration, no set certification; select liveness/fairness only EMPIRICALLY tested in Go with sleeps (TestSelectLiveness*, channel_test.go:897-1018@3be88bb) — properties their logic does not state | **CAP** on their side |
| O7 | The sequential-conservation theorem (`execProg_single_eq_execStmt`): every sequential result in the transferable classes is the pool result verbatim — 33 sequential designated statements transfer unrestated; corpus bit-identity as the empirical twin | slice-2 log, `MultiSound.lean` | No analogue needed (no sequential machine) — but nothing plays this role of a machine-level growth-by-extension guarantee | ours-specific asset |
| O8 | ∀-schedule KERNEL certificates + a concurrent termination notion: `forkJoinAllSchedules42/NoDeadlock/NoRace`, `TerminatesNormallyC` (one fuel bound, every stream, main-normal) — designated statements (5 of the 44 — indices stale-corrected at audit F14) | `proofs/Audit.lean` designated list; `MultiStreams.lean` | Partial correctness only; explicitly no termination/liveness/fairness claims anywhere (research note §3; enumeration §5) | **CAP** on their side |
| O9 | Faithful main-exit (main's return terminates the program; goroutine leaks classified) | D6; goroutines/main-exit | Pool never removes threads — a safety-conservative SUPERSET (research note §3): sound for them, observationally unfaithful | **LAT** (their too-wide is free under safety-only; ours is oracle-required) |
| O10 | Nil channels inside select | channels/select-nil-default (green) | NOT modeled: their model's `TrySend/TryReceive` have no nil check (channel.go:46-98,120-181@3be88bb — only Send/Receive/Close/Len/Cap check nil); a nil clause would nil-deref in the Go model and is unprovable in Coq (`is_chan` requires `ch ≠ chan.nil`, chan_au_base.v:449); no test covers it | **CAP** on their side |
| O11 | Blocked-config machine states (no spin): O(1) blocking, fuel-friendly, wake as explicit pairing, waiter-queue-priority arrival matching gc's recvq-before-buffer discipline with the re-argued hchan invariant | S2 audit-response redesign (`arrivalPlan`) | Spin loops + mutex; buffered channels post NO offers, so gc's direct-handoff observation (len 0 beside a parked receiver) is not enforced — their model can expose len-transients real gc avoids; they explicitly punt on len reasoning ("might not be worth specifying", channel.go:250-251@3be88bb) | **LAT** — their envelope is wider than gc with no oracle; exactly the class our S2 audit fixed on our side |
| O12 | Statement-TCB discipline: first-order designated statements over the interpreter, comparator-judge independent kernel replay, non-vacuity discharge witnesses per law | CLAUDE.md doctrine; Audit.lean gate | Client-facing channel reasoning is irreducibly higher-order Iris (nested-mask AUs, saved-prop offer parking); no analogue of statement-TCB review or witness gating (their `False`-branch AUs are the vacuity smell our gate exists for, though theirs are deliberate) | **DEL** difference of doctrine |
| O13 | Adversarial-input validation at scale: grossmith fuzzer campaigns (2,900 cases vs the channels-arc tip, zero divergences) | `.tmp/grossmith-campaign-2026-08-07.md` (main repo) | No fuzzing of translation or semantics found | ours-specific asset |

## A.4 Spec-latitude / envelope differences (neither side "wrong"; argued vs spec text)

| # | Site | Theirs | Ours | Assessment |
|---|---|---|---|---|
| L1 | Select ready-choice | Demonic permutation PER ATTEMPT; blocking select re-issues the whole SelectStmt with a fresh permutation each retry (defn/chan.v:98,109@43d4efa) → the envelope admits starving a perpetually-ready case forever | L2 "any entry-ready case" at entry; NO re-randomization on the blocked path — a woken select head-commits the first wake-ready clause, wake-order latitude delegated to L1/L4 (D4; slice-4 L2 site) | [ANALYSIS] Both weaken "uniform pseudo-random" possibilistically. Theirs is strictly wider (starvation members — harmless under no-liveness, fatal if they ever want termination). Ours is deliberately narrower on the wake path with the recorded argument (every gc first-event commit realized by a prompt-wake schedule). Their own Go tests empirically DEMAND liveness (TestSelectLiveness*) their semantics doesn't guarantee — a model/test mismatch worth citing in reviews |
| L2 | Waiter/wake order | Unconstrained (whichever spinner wins the mutex); nothing recorded | L4 "any matching waiter", width = #matches, membership point; gc FIFO noted as a membership sample | parity in effect; only we carry the envelope statement + width metadata |
| L3 | Scheduling granularity | Any interleaving at sub-expression granularity, threads never blocked | Any schedule over RUNNABLE threads at registry granularity (L1) | [ANALYSIS] theirs wider (fine-grain + spinners always runnable); ours needs the NPDRF reduction to claim equal observational envelope for DRF programs — the open obligation (T12) |
| L4 | Buffered send beside parked receiver | Value transits the buffer (no waiter priority) — len-transient observable | gc's waiter-priority handoff, len preserved (S2 redesign) | ours matches gc's realized observations; theirs is a wider unvalidated envelope (see O11) |
| L5 | Main exit | Superset (threads keep stepping) | Faithful termination | see O9 |
| L6 | select arity in the EXECUTABLE model | Go-side model helpers exist only for 1-3 cases (select.go@3be88bb, whole file; `RandomUint64()%n` coin); GooseLang `try_select` is any-arity | any arity end to end | note for test-import: their >3-case surface is untested even in Go; the coin↔permutation correspondence is trusted (select.go:3-5) |
| L7 | Channel panics | modeled in the Go model, UB-by-obligation in the logic | modeled + recoverable everywhere | see O5/T12 |

## A.5 Their verified channel-example set (the spec-level witness targets)

[FACT] `new/proof/.../examples/channel*.v@43d4efa`: hedged requests
(`wp_CancellableHedgedRequest`, using `wp_select_blocking`), hello-world
async/sync/cancellable/with-timeout, `wp_simple_join`/`wp_simple_multi_join`,
`wp_exchangePointer`, `wp_BroadcastExample`, the select-tricky trio (incl.
the proved-unreachable default), the dsp examples (`wp_DSPExample`,
Serve/Client/MapServer/MapClient/Muxer), higher-order, search-replace,
workq, etcd_session, elimination_stack, lock — ~55 wp lemmas total, 0-1
Admitted. Explicitly unverified variants exist (`cv_unverified.go`,
`muxer_unverified.go`, `leaky_buffer_unverified.go` — Cond is the recurring
reason). [ANALYSIS] This list is the natural witness-target set for our
T3/T4/T7 successor arc: when the spawning frame-quantified `GoSpecC` and the
channel law family land, "we can state and discharge GoSpecC instances for
their verified channel examples" is the parity claim to aim at, program by
program.

## A.6 Headline

Counts (rows above): **12 items they have that we lack** (A.2: 8 CAP, 3
DEL-with-record, 1 DEL+open-debt), of which the concrete successor-arc set
is {sync (T1), atomics (T2), channel WP law family (T3+T4), idioms/protocols
(T5+T6), spawning frame-quantified GoSpecC (T7)} — all already recorded as
owed work in the design note except T5/T6, which land after T3. **13 items
we have that they lack** (A.3), the structural ones being executability +
differential validation (O1/O2), observable deadlock (O3), tested race
semantics (O4), certified select nondeterminism (O6), and ∀-schedule
termination-grade kernel theorems (O8). **7 spec-latitude differences**
(A.4), none a bug on either side; two of theirs (L1 starvation-width, L4
len-transients) are too-wide-without-oracle shapes our doctrine would flag.

[ANALYSIS] Net position: at channel BEHAVIOR level we cover their
capabilities and more (A.1 + O3-O6, O10). At channel SPEC level they are far
ahead (T3-T7): we ship kernel certificates and history predicates where they
ship a reusable logically-atomic law library plus idioms. The gap is exactly
the recorded decomposition/successor arc; their AU catalog + the documented
canonical-weakest-spec problem (chan_au_base.v:244-263) is the best existing
map of what channel laws clients need, and each one we adopt must carry a
discharge witness per our non-vacuity gate.

---

# PART B — Their full test-example inventory vs GoLean today

Source: fresh enumeration of `deps/goose` testdata/go_test/test/model trees
and `deps/perennial/new` proofs @ the pinned revs; counts are [FACT] from
`find`/`grep` over the working trees.

## B.1 Tree map

| Tree | Purpose | .go files |
|---|---|---|
| `testdata/examples/unittest` (+externalglobals, generics, generics/helpers) | Translation golden tests, gold `unittest.gold.v` | 56 (~236 funcs) |
| `testdata/examples/semantics` | Executable corpus: `test*() bool` oracles; `cmd/test_gen` emits `generated_test.go` (testify suite asserting each `testXxx() == true`); run by plain `go test` | 33 (308 funcs; **112 `test*` + 3 `failing_test*` oracles**) |
| `testdata/examples/channel` (+5 subdirs) | Channel/goroutine example programs, several with real `_test.go` | 23 (~110 funcs) |
| storage examples (`append_log, wal, simpledb, logging2, async, comments, mapliteral, mutualrec, interfacerecursion, import`) | Whole-program golden tests | 12 |
| `testdata/negative-tests`, `goose-tests`, `disabled-tests`, `proofsetup-tests` | `// ERROR`-marker rejection tests / CLI fixtures | 8 |
| `go_test/` | Native Go-behavior demonstration tests | 1 file, 25 Test funcs |
| `model/{channel,go_channel,strings}` | The executable models + native twin (Part A) | 9 |

Total testdata .go files: **132**. **No `func main()` anywhere in
testdata**; everything is library packages of top-level functions.

Their harness mechanisms [FACT]: golden-output string compare
(`deps/goose/examples_test.go:119,145-160@3be88bb`), `// ERROR` negative
markers (:231,245-262), `test_gen` boolean-oracle suite
(`cmd/test_gen/main.go:129,145`; `disk.Init(NewMemDisk(30))` in SetupTest),
bats CLI tests (`test/goose.bats`). On the Coq side, semantics tests are
PROVED, not executed: `test_fun_ok name := ∀ Φ, Φ #true -∗ WP @! name #()`
with a `semantics_auto` tactic
(`new/proof/.../semantics_proof/semantics_init.v:25-51@43d4efa`) — **28 of
the 112 oracles are proved** (36 `test_fun_ok` lemma STATEMENTS exist;
28 `Qed`, 7 `Abort`, 1 `Admitted`; the suite's 29th `Qed` is the
non-oracle `wp_shouldPanic`). [CORRECTION OF RECORD 2026-08-10,
spec-parity S3 audit: this line originally read "**37 of the 112
oracles are proved** (1 Admitted)" — 37 counted lemma statements (36
`test_fun_ok` + `wp_shouldPanic`), silently including the 7 `Abort`s
and the `Admitted` as proved. Measured:
`grep -h 'Qed\.' *.v | wc -l` = 29,
`grep -rn 'test_fun_ok semantics\.' *.v | wc -l` = 36,
`grep -h 'Abort\.' *.v | wc -l` = 7 over semantics_proof/ @ 43d4efa.
The standing restatements — the comparison matrix (×2), the
end-of-buildout report, the arc charter (basis + slice-3 record), the
S3 slice note and manifest — were corrected the same round; the
buildout log's historical batch-entry mention carries an in-place
annotation (delta-review sweep: the first version of this sentence
claimed "every tracked restatement" while that line was still
unannotated).]

## B.2 Dependency classification

Import frequency across all 132 testdata files [FACT]: sync 17, time 10,
testing 8, primitive/disk 8, primitive 5, fmt 5, strings 4, encoding/binary
4, marshal 3, sync/atomic 2, singletons (strconv, errors, log, std, filesys,
async_disk, grove_ffi, testify) 1 each. **45 files have imports; 87 have
none; of the 87, 7 (all in examples/channel) use `chan`/`go` with zero
imports — 80 files are fully clean** (pure Go, no imports, no concurrency).

Counts per class × tree:

| Class | unittest (56) | semantics (33) | channel (23) | storage (12) | total blocked |
|---|---|---|---|---|---|
| imports-clean, concurrency-free | 43 | 29 | 0 | 5 | — (80 importable) |
| imports-clean + channels/goroutines only | 2 (chan.go; spawn.go also sync) | 0 | 7 | 0 | 0 for us NOW (channels arc shipped) |
| needs-sync | 4 (condvar, locks, synchronization, spawn) | 3 (lock, prims†, wal†) | 6 | 5† | **17** |
| needs-atomics | 0 | 0 | 1 (workq) | 1 (import.go, blank import) | 2 |
| needs-FFI/disk (primitive, disk, filesys, grove) | 4 | 2† | 1 | 6† | **17** distinct |
| needs-time | 0 | 0 | 10 | 0 | 10 |
| other stdlib (fmt/strings/binary/log/…) | 3 | 0 | 3 | 4 | ~12 |
| harness files (testing/testify) | 0 | 1 | 5 | 0 | 8 |

† overlap: the FFI column double-counts sync users (append_log, wal,
logging2, simpledb, semantics/wal, prims). sync primitive spread: Mutex ~11
files, Cond 2, RWMutex 1 (simpledb), WaitGroup 1 (parallel_search_replace).
Only build-tag file: goose-tests/errors/build_tag/bad.go. Generics: 3
unittest files (we have a generics lane — expected exportable).

## B.3 Would it export / run / verify under GoLean today?

**(1) Export.** Our frontend refuses ALL imports (imported named
types/methods fail closed, `tools/nativefrontend/emit.go:4105,4148`) and
supports only single-file executable packages
(`Corpus/coverage/README.md:20-25`). So: the 45 import-bearing files do not
export today (sync/atomics/FFI/time/fmt all land in the same refusal class);
the 87 no-import files are candidates, MINUS a per-file caveat: unittest and
semantics are each ONE package spread across files, so a file whose
functions call helpers in a sibling file needs package assembly into a
standalone single file (mechanical concatenation; self-containment must be
checked per file — not quantified in this pass). The 7 clean channel files
(muxer, fibonacci, google_search, higher_order, actris_example,
select_tricky_examples, muxer_unverified) exercise exactly the machinery the
channels arc shipped; expected to export, with any refusal landing in our
recorded fail-closed classes (select-with-select rendezvous,
dead-recv-len-operand, bare-recover statement, go-of-nil-func fatal).
IMPORT-LANE CALIBRATION (arc-final audit F21/F23, 2026-08-08): the
dead-recv-len-operand entry above names BUG-032's class by its
artificial discriminator; its REAL trigger is broad — `len`/`cap` of
any non-identifier/literal/value-selector operand anywhere in a
receive-bearing function — and a hit inside a METHOD aborts the whole
package export (methods have no per-decl quarantine; receive-bearing
decls in raft are 12/12 methods). Budget import triage accordingly;
the class statement lives in BUG-032 (docs/BUGS.md).

**(2) Differential run.** They are translation tests, not oracles — except
the semantics corpus, whose 112 `test*() bool` functions are EXACTLY our
corpus convention (subject function returning an observable value, harness
generates main and strips any handwritten one —
`Corpus/coverage/README.md:28-36`; their `test_gen` already automates the
same wrapping, regex at main.go:129 reusable). Adaptation shapes, by tree:
semantics → mechanical `cases.tsv` rows (`expected_status: ok`, subject =
testXxx; their 3 `failing_test*` become expected-fail/negative rows);
unittest → functions have NO oracle (they exist to exercise translation) —
each needs an authored wrapper computing a checksum/observable (the wrapper
is harness-side; the imported body stays verbatim); channel examples → wrap
entry points with deterministic arguments, lane per D9 (confluent for
deterministic concurrent shapes, membership where schedule-dependent — their
sleep/timeout-based tests must NOT be imported as-is; the enumerator
replaces their probabilistic scheduling); storage/FFI → blocked regardless.

**(3) "Verify" for their PROVED examples.** Three rungs, mapping their
artifact to ours: (i) their 28 proved `test_fun_ok` semantics proofs (of
36 stated — count corrected 2026-08-10, see B.1) → our
TotalPins-style kernel theorems (`TerminatesNormally` + readout `= true`) —
mechanizable en masse over every imported clean oracle, i.e. we can EXCEED
their 28 by proving ~all 100+ clean oracles with `decide +kernel`
certificates, the exact pipeline the designated set already exercises;
(ii) their channel-example wp proofs (~55 lemmas, A.5) → GoSpecC instances —
BLOCKED on T3/T7; until then the honest analogue is ∀-schedule checker
certificates (`allStreamsOkPool`) for the confluent ones; (iii) their
sync/atomic/stdlib proofs → out of scope until the phases below.

## B.4 Blocker ranking (files unlocked per capability)

1. **sync** — 17 files (Mutex 11; +Cond 2, RWMutex 1, WaitGroup 1). The
   expectation "sync dominates" holds for the main unittest+semantics
   corpora; corpus-wide the channel tree (22 files) was the largest class,
   but the channels arc already unlocked that machinery — sync is now the
   top LIVE blocker. Net unlock from a sync slice alone (no FFI): ~11
   files; with a time model too: +6 sync∩time channel-tree files.
2. **FFI/disk/grove** — 17 distinct files. DEL per T9 (north star needs
   none); out-of-scope absent a target change.
3. **time** — 10 files (all channel tree). Needs a time-model decision
   (sleep-elision vs abstract clock); raft's Tick is channel-driven, so a
   minimal model may suffice.
4. **testing/testify harness files** — 8; never import targets (their role
   is played by our cases.tsv + runner).
5. **other stdlib (fmt/strings/binary/…)** — ~12 files; rides T10.

## B.5 [PROPOSAL] The phased import campaign ("verify them all", scoped)

- **Phase 1 — import what exports today: 87 candidate files** (80 clean +
  7 concurrency-clean channel examples), headlined by the 29 clean
  semantics files carrying ~100 boolean oracles → ~100 new strict-lane rows
  with mechanical expectations, plus authored-wrapper unittest cases and
  confluent/membership-lane channel examples. Deliverables: provenance-
  tagged corpus rows (Part C), a per-file export report (any refusal must
  land in a recorded fail-closed class — a NEW refusal reason is a
  finding), and rung-(i) kernel certificates for imported oracles (target:
  exceed their 28 proved semantics tests — count corrected 2026-08-10,
  see B.1 — in the first movement). The
  packaging step (single-file assembly + wrapper authoring for unittest) is
  the only non-mechanical part.
- **Phase 2 — the sync slice: +~11 files** (17 minus FFI-overlap), via the
  registry growth contract (Mutex/RWMutex/WaitGroup/Once each = one
  scheduling point + one HB edge rule; Cond fail-closed until pinned —
  their notifyList stubs are the warning sign). Raft-critical and the
  `FairStream` prerequisite when atomics follow (then workq's atomics file
  too). A time-model decision adds the 10 time files.
- **Phase 3 — the remainder, with reasons**: FFI/disk (17) — deliberately
  out of scope (T9; record in the matrix); other-stdlib (~12) — awaits the
  stdlib strategy (T10); harness files (8) — not targets by construction;
  their `// ERROR` negative markers — import as negative-lane candidates
  where they map to Go-illegal programs.
- Rung-(ii) "verify their proved channel examples" at spec level is NOT an
  import-campaign phase — it is the successor proof arc (T3/T4/T7), and
  A.5's list is its witness-target set.

---

# PART C — [PROPOSAL] The standing comparative-audit mechanism

1. **A standing comparison matrix in docs/** —
   `docs/goose-perennial-comparison.md` (this discharges the existing
   TODO.md "Goose/Perennial Design Mapping" entry, TODO.md:359-377, which
   already names the areas and anchors). Content: Part A's tables as living
   rows — `capability | theirs (file:line@rev) | ours (file:line / corpus
   id / theorem) | classification (CAP/DEL/LAT) | last-reviewed (arc)`.
   Maintenance contract: (a) updated in the SAME arc that changes a row's
   truth (the design-note-per-arc comparison practice already in CLAUDE.md
   gets one canonical home); (b) deps revs pinned in the header — rev bumps
   are deliberate recorded events (fetch upstream via `git log origin` or
   scratch clones; never mutate the pinned checkouts); (c) DEL rows carry
   their recorded reason + a revisit trigger; CAP rows link the owing
   TODO/arc entry.
2. **A comparative reviewer dimension in the arc-final audit** (charter
   sketch, subject to the user's audit-plan sign-off each time per the
   merge protocol): one decorrelated Opus reviewer per arc-final audit
   whose brief is (i) verify every matrix row the arc touched against
   PRIMARY sources at the pinned revs; (ii) hunt upstream movement (their
   in-tree raft/etcd effort is active — 51 Admitteds being discharged over
   time) and new capabilities; (iii) flag any GoLean claim of the form
   "covers X like Goose" that the matrix does not ground. Findings ground
   to file:line@rev on BOTH sides; cadence = arc-final only, not per-slice.
3. **The import pipeline as a corpus lane** — provenance-tagged, never
   edited:
   - Layout: `Corpus/coverage/exec/imported-goose/<tree>/<case>/main.go`
     with a mandatory provenance header comment (upstream path @ rev,
     import date, transform applied), plus the ordinary `cases.tsv`
     (features gain an `imported_goose` tag; no schema change needed).
   - Invariant: imported function bodies are VERBATIM — permitted
     adaptation is only (a) package assembly (concatenating sibling-file
     helpers of the same upstream package), (b) appended wrapper subjects
     below a `// --- GoLean harness ---` marker, (c) a `main`. The
     differential oracle stays `go run` on the assembled file, so
     canonical-Go-is-the-input is preserved; "do not edit canonical Go to
     make something pass" applies with full force — an imported case that
     fails stays red or gets a recorded fail-closed classification.
   - A small `scripts/import-goose` helper: given upstream file(s) + rev,
     emits the assembled case + provenance header + skeleton cases.tsv
     rows; re-import = re-run at the pinned rev; upstream drift = a
     recorded rev bump (mirroring baseline re-pin discipline).
   - Their spec-sentence-keyed channel tests (channel_spec_test.go /
     channel_test.go shapes) import under the same rule — the posture the
     channels-arc design note already recorded ("imported as fresh
     canonical corpus inputs with provenance"). Note: NO goose-provenance
     cases exist in the corpus yet (grep verified) — this lane starts
     empty, so phase 1 is its first population.

Open questions for the user (recorded, not decided here): whether phase 1
lands as one arc or as a background lane; whether the time model is a
phase-2 co-requisite or its own decision; whether rung-(i) kernel
certificates for imported oracles join the designated set (44 → ~140 would
strain statement-TCB review — a SAMPLED designation policy is probably
right and needs its own sign-off).
