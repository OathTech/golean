# Goose/Perennial comparison — the standing matrix

The living capability-comparison matrix proposed by
`docs/2026-08-07_goose-comparative-scoping.md` Part C (seeded 2026-08-07
from its Part-A tables, verbatim rows reformatted into the standing
shape). This discharges the old TODO.md "Goose/Perennial Design Mapping"
entry: this file is the canonical home for the per-arc comparison
practice CLAUDE.md records (design comparisons land in the arc's design
note AND update their rows here).

## Maintenance contract

- **Updated in the SAME arc that changes a row's truth.** A slice that
  closes a CAP, adds a capability, or changes a latitude updates the row
  with a new `last-reviewed` stamp in that arc.
- **Pinned revisions** (all their-side cites below are at these; rev
  bumps are deliberate recorded events — fetch upstream via `git log
  origin` or scratch clones, never mutate the pinned checkouts):
  - `deps/goose` @ `3be88bbb4982f58e5813b6f0344302d5582c8e8a` (branch
    `new`; cited `@3be88bb`). Upstream development has moved into
    mit-pdos/perennial (goose README) — upstream drift check owed at
    each review.
  - `deps/perennial` @ `43d4efabc22eb148eb239ebee89d1dd2ee54c900`
    (master; cited `@43d4efa`).
- **Classification key**: **CAP** = capability gap (close eventually;
  the row links the owing record), **DEL** = deliberate divergence
  (the row carries the recorded reason + revisit trigger), **LAT** =
  spec-latitude difference (both defensible; envelope shapes differ).
- The arc-final audit's comparative reviewer dimension (scoping note
  Part C item 2, subject to per-audit sign-off) verifies rows the arc
  touched against primary sources and hunts upstream movement.

## 1. Behavior-level parity (both sides model these, agreeing with gc)

Last-reviewed: channels arc, 2026-08-07 (seeding). [FACT] rows; their
cites from the scoping enumeration, ours from the design-note slice
logs + corpus ids.

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

## 2. They have, we lack

Last-reviewed: channels arc, 2026-08-07 (seeding).

| # | What | Their evidence | Our status | Class |
|---|---|---|---|---|
| T1 | `sync` package: Mutex/RWMutex/WaitGroup/Once/sema specs proved over the goose-translated REAL stdlib source, atop a small trusted core (Mutex→CmpXchg spinlock, semaphore model; Cond notifyList STUBBED no-ops) | `new/trusted_code/sync.v:8-58@43d4efa`; `new/proof/sync.v` + `sync_proof/*` (9 files, ~35 wp lemmas) | Nothing. Recorded growth contract: a sync primitive is added by REGISTERING it (one scheduling point + one HB rule), design note D2+D3 | **CAP** — the top live blocker for their corpus (scoping Part B) and raft-critical; owed: successor sync arc |
| T2 | `sync/atomic`: machine atomics (`LoadOp/AtomicSwap/AtomicAdd/CmpXchg`, lang.v:84-105,1372-1431@43d4efa) + 49 wp lemmas (`new/proof/sync/atomic.v`, their largest single proof file) | ibid. | Nothing; D5 records atomics as the `FairStream` prerequisite arc | **CAP** — owed: atomics arc (FairStream prerequisite) |
| T3 | Logically-atomic channel-op spec set: `send_au/recv_au/close_au` + nested AUs + two incomparable nonblocking variants; proved `wp_NewChannel/wp_Send/wp_Receive/wp_Close/wp_TrySend/wp_TryReceive/wp_Len/wp_Cap` | `chan_au_base.v:106-297@43d4efa` (canonical-weakest-spec problem documented at :244-263); `chan_au_{new,send,recv}.v` | ZERO channel WP/lifting laws — our concurrent Iris layer has only `wpC_fork`/`wpC_pure_det`/`wpC_spawned_strip` (`proofs/GoLeanProofs/LangC.lean`); channel facts export as operational history predicates / kernel certificates instead | **CAP** (deliberately deferred — slice-5 record: "no consumer this slice, no inert scaffolding"; lands with the decomposition arc) |
| T4 | Select WP specs: `wp_select_blocking` (`[∧ list]` per-case AUs), `wp_select_nonblocking`, `wp_select_nonblocking_alt` (∗-separated with not-ready witnesses → provable-unreachable default) | `theory/chan.v:272-299,427-455,584-619@43d4efa`; unreachable-default demo `wp_select_nb_guaranteed_ready`, channel_select_tricky_examples.v:117 | None (same deferral as T3) | **CAP** (with T3) |
| T5 | Channel idiom spec libraries: bag, broadcast, contrib (Actris ghost theory), future, handshake, lock, mpmc (1022 ln), spsc (668 ln) | `theory/chan/idioms/*@43d4efa` | None. [ANALYSIS] their idiom set is a map of raft's channel patterns — broadcast/done-channel and bag are what `v3_proof/protocol.v` imports | **CAP** (successor-arc, after T3) |
| T6 | dsp/ — Actris dependent separation protocols over PAIRS of Go channels, with proofmode tactics (`wp_recv`/`wp_send`) and the COFE model in-tree | `theory/chan/idioms/dsp/{dsp,dsp_ghost_theory,proto_model,dsp_proofmode}.v@43d4efa`; example `wp_DSPExample` channel_dsp.v:35 | None (the "Actris-lite" layer named in D8 was deliberately not built in slice 5) | **CAP** (lowest urgency of the spec-layer family) |
| T7 | Frame-quantified WP proofs over genuinely-spawning programs (their entire proof portfolio is this) | e.g. `wp_simple_join` channel.v:259, all of §5's examples | RECORDED SUCCESSOR DEBT: `goldenSpecC` is the sequential-degenerate lane; the spawning frame-quantified `GoSpecC` needs the pairing decomposition (pool `StepM` pairing touches two threads; iris-lean `Language` steps one) — slice-5 log + Surface.lean witness-status note | **CAP** (the named next-arc obstruction, sized) |
| T8 | Prophecy variables (HeapLang-inherited; used at scale in vMVCC) | lang.v:244-245@43d4efa | None; slice-5 log records "no prophecies needed — primitive channels make lifting laws the atomic specs" | **DEL** for channels; revisit trigger: a future target needing future-dependent linearization |
| T9 | Crash semantics + FFI worlds (disk, async_disk, filesys, grove network) and the storage-systems portfolio | lang.v FFI parameter; `testdata/examples/{append_log,wal,simpledb,...}` | Out of scope: our north star (etcd-io/raft, the library) needs no disk/net FFI | **DEL** — revisit trigger: a target change |
| T10 | Translated Go stdlib surface: sync, atomic, time, strings, bytes, sort/slices (real stdlib pdqSort proved), context, fmt, encoding/binary, errors, io, log, math… | `etc/ci-goose-check.py:23-41@43d4efa` pins the source repos; `new/code/*`; ~60 stdlib wp lemmas + ~25 slices/sort | Our frontend refuses imports (`tools/nativefrontend/emit.go:4105,4148` — imported named types/methods fail closed) | **CAP** long-term; scoping Part B quantifies which corpus files this blocks |
| T11 | North-star proof progress: in-progress etcd-raft + etcd verification (`wp_Node__Propose` Qed; etcd client 39 wp lemmas but 29 Admitted; readonly.v 955 ln, 5 Admitted) | `new/proof/go_etcd_io/raft/v3.v:17-29`, `v3_proof/*`, `etcd/client/*@43d4efa`; Go sources external: github.com/upamanyus/{etcd-raft,etcd} branch `goose` | Our quorum pilot is a raft fragment; no raft-package-scale work yet | **CAP** (this is the race; their surface is demonstrably WIP — 51 Admitted across new/proof's 376 wp lemmas) |
| T12 | Sub-step interleaving granularity + operational race-UB by construction (two-step na accesses, `naMode Reading n | Writing`; racy access → stuck) | lang.v:543-546,1352-1396@43d4efa | We rejected naMode (grows by revision, D2+D3); registry-granularity + the NPDRF reduction OBLIGATION, whose statement is currently a REFUTABLE-as-written draft (NPDRF.lean; S3 audit) | **DEL** with an honest open metatheory debt on our side — their granularity story is complete by construction; ours rests on the unproven reduction |

## 3. We have, they lack

Last-reviewed: channels arc, 2026-08-07 (seeding).

| # | What | Our evidence | Their status | Class |
|---|---|---|---|---|
| O1 | An executable semantics at all + `go run` differential validation (1194 exec + 311 negative cases, six-lane taxonomy, tracked baseline, zero-drift gates) | design note D9; `baselines/native-full.tsv` | Their GooseLang interpreter + semantics corpus was DELETED with the old semantics (perennial `eb748d43e`, 2026-01-30); the new semantics has NO interpreter and no differential harness (research note §5; `cmd/test_gen -coq` still references the absent `Perennial.goose_lang.interpreter`) | **DEL** on their part (casualty of the rewrite); our differentiator |
| O2 | Channel-model validation IN the trusted semantics: our interpreter IS the model under differential test. Their Go-model tests are real and good (spec-sentence-keyed `channel_spec_test.go:15-98@3be88bb`; runtime-derived + in-process model-vs-native differential `channel_test.go:210-310,447-622`; the `model/go_channel` native twin re-running the identical corpus) but validate the GO model — the model↔GooseLang correspondence and select-model↔`try_select`-axioms are TRUSTED, stated in their own header (select.go:3-5@3be88bb) | — | trust gap on their side | our structural advantage |
| O3 | Deadlock as an observable terminal matching gc ("all goroutines are asleep - deadlock!", exit 2), differentially tested (`expected_status: deadlock`) | slice-1/2 logs; channels/deadlock, goroutines/deadlock | Impossible: blocked = spin loops; a deadlocked program just diverges. No counterpart of Go's runtime detector | **CAP** on their side |
| O4 | In-machine race DETECTION: segment-HB vector clocks (TSan/FastTrack skeleton), HB edges quoted against go_mem at implementation sites, `raceDetected` terminal, racy lane "every enumerated path refuses" + `go run -race` (exit 66) as justifying oracle; DRF-SC boundary pinned executably (sb-chan {1,10,11}, 00 mechanically excluded) | slice-3/4 logs; `GoLean/GoCore/Race.lean` inventory | naMode makes races UB/stuck for PROOFS but is untestable — "Goose has no way to test its race semantics at all" (research note §4); no -race oracle use anywhere | **CAP** on their side |
| O5 | Recoverable channel panics: send-on-closed/close-of-closed/close-of-nil/make-negative are real Go panics — `recover()` works, messages differentially compared | channels/close-edge/recover-* (all green) | In the logic these are `False` branches in `send_au`/`close_au` (chan_au_base.v:205,295@43d4efa) — verified code must prove them impossible; `go.panic` has no proof rules found; the Go-model panics are unreachable-by-obligation. Go defines these as catchable panics | **DEL** on their side (proof-obligation style); faithfulness + testability win on ours |
| O6 | Select multi-ready with a CERTIFIED possibilistic record: L2 envelope statement at the site, membership lane with machine-enumerated observation sets + `members=n` cardinality pins, plain AND -race dual go-run sampling | slice-4 log; channels/select-multi-ready/observable {101,210}, select-wake-multi {1,2}, select-arrival-multi {10,20} | Nondeterminism exists (demonic permutation) but is unexplored: no schedule enumeration, no set certification; select liveness/fairness only EMPIRICALLY tested in Go with sleeps (TestSelectLiveness*, channel_test.go:897-1018@3be88bb) — properties their logic does not state | **CAP** on their side |
| O7 | The sequential-conservation theorem (`execProg_single_eq_execStmt`): every sequential result in the transferable classes is the pool result verbatim — 33 sequential designated statements transfer unrestated; corpus bit-identity as the empirical twin | slice-2 log, `MultiSound.lean` | No analogue needed (no sequential machine) — but nothing plays this role of a machine-level growth-by-extension guarantee | ours-specific asset |
| O8 | ∀-schedule KERNEL certificates + a concurrent termination notion: `forkJoinAllSchedules42/NoDeadlock/NoRace`, `TerminatesNormallyC` (one fuel bound, every stream, main-normal) — designated statements | `proofs/Audit.lean`; `MultiStreams.lean` | Partial correctness only; explicitly no termination/liveness/fairness claims anywhere (research note §3; enumeration §5) | **CAP** on their side |
| O9 | Faithful main-exit (main's return terminates the program; goroutine leaks classified) | D6; goroutines/main-exit | Pool never removes threads — a safety-conservative SUPERSET (research note §3): sound for them, observationally unfaithful | **LAT** (their too-wide is free under safety-only; ours is oracle-required) |
| O10 | Nil channels inside select | channels/select-nil-default (green) | NOT modeled: their model's `TrySend/TryReceive` have no nil check (channel.go:46-98,120-181@3be88bb — only Send/Receive/Close/Len/Cap check nil); a nil clause would nil-deref in the Go model and is unprovable in Coq (`is_chan` requires `ch ≠ chan.nil`, chan_au_base.v:449); no test covers it | **CAP** on their side |
| O11 | Blocked-config machine states (no spin): O(1) blocking, fuel-friendly, wake as explicit pairing, waiter-queue-priority arrival matching gc's recvq-before-buffer discipline with the re-argued hchan invariant | S2 audit-response redesign (`arrivalPlan`) | Spin loops + mutex; buffered channels post NO offers, so gc's direct-handoff observation (len 0 beside a parked receiver) is not enforced — their model can expose len-transients real gc avoids; they explicitly punt on len reasoning ("might not be worth specifying", channel.go:250-251@3be88bb) | **LAT** — their envelope is wider than gc with no oracle; exactly the class our S2 audit fixed on our side |
| O12 | Statement-TCB discipline: first-order designated statements over the interpreter, comparator-judge independent kernel replay, non-vacuity discharge witnesses per law | CLAUDE.md doctrine; Audit.lean gate | Client-facing channel reasoning is irreducibly higher-order Iris (nested-mask AUs, saved-prop offer parking); no analogue of statement-TCB review or witness gating (their `False`-branch AUs are the vacuity smell our gate exists for, though theirs are deliberate) | **DEL** difference of doctrine |
| O13 | Adversarial-input validation at scale: grossmith fuzzer campaigns (2,900 cases vs the channels-arc tip, zero divergences) | `docs/2026-08-07_grossmith-campaign.md` | No fuzzing of translation or semantics found | ours-specific asset |

## 4. Spec-latitude / envelope differences (neither side "wrong"; argued vs spec text)

Last-reviewed: channels arc, 2026-08-07 (seeding). See also the
envelope-width review over L1/L2/L4 in the channels-arc design note's
slice-6 build log.

| # | Site | Theirs | Ours | Assessment |
|---|---|---|---|---|
| L1 | Select ready-choice | Demonic permutation PER ATTEMPT; blocking select re-issues the whole SelectStmt with a fresh permutation each retry (defn/chan.v:98,109@43d4efa) → the envelope admits starving a perpetually-ready case forever | L2 "any entry-ready case" at entry; NO re-randomization on the blocked path — a woken select head-commits the first wake-ready clause, wake-order latitude delegated to L1/L4 (D4; slice-4 L2 site) | [ANALYSIS] Both weaken "uniform pseudo-random" possibilistically. Theirs is strictly wider (starvation members — harmless under no-liveness, fatal if they ever want termination). Ours is deliberately narrower on the wake path with the recorded argument (every gc first-event commit realized by a prompt-wake schedule). Their own Go tests empirically DEMAND liveness (TestSelectLiveness*) their semantics doesn't guarantee — a model/test mismatch worth citing in reviews |
| L2 | Waiter/wake order | Unconstrained (whichever spinner wins the mutex); nothing recorded | L4 "any matching waiter", width = #matches, membership point; gc FIFO noted as a membership sample (directed pin goroutines/sched-dependent/waiter-pick, slice 6) | parity in effect; only we carry the envelope statement + width metadata |
| L3 | Scheduling granularity | Any interleaving at sub-expression granularity, threads never blocked | Any schedule over RUNNABLE threads at registry granularity (L1) | [ANALYSIS] theirs wider (fine-grain + spinners always runnable); ours needs the NPDRF reduction to claim equal observational envelope for DRF programs — the open obligation (T12) |
| L4 | Buffered send beside parked receiver | Value transits the buffer (no waiter priority) — len-transient observable | gc's waiter-priority handoff, len preserved (S2 redesign) | ours matches gc's realized observations; theirs is a wider unvalidated envelope (see O11) |
| L5 | Main exit | Superset (threads keep stepping) | Faithful termination | see O9 |
| L6 | select arity in the EXECUTABLE model | Go-side model helpers exist only for 1-3 cases (select.go@3be88bb, whole file; `RandomUint64()%n` coin); GooseLang `try_select` is any-arity | any arity end to end | note for test-import: their >3-case surface is untested even in Go; the coin↔permutation correspondence is trusted (select.go:3-5) |
| L7 | Channel panics | modeled in the Go model, UB-by-obligation in the logic | modeled + recoverable everywhere | see O5/T12 |

## 5. Their verified channel-example set (the spec-level witness targets)

Last-reviewed: channels arc, 2026-08-07 (seeding). [FACT]
`new/proof/.../examples/channel*.v@43d4efa`: hedged requests
(`wp_CancellableHedgedRequest`, using `wp_select_blocking`), hello-world
async/sync/cancellable/with-timeout, `wp_simple_join`/
`wp_simple_multi_join`, `wp_exchangePointer`, `wp_BroadcastExample`, the
select-tricky trio (incl. the proved-unreachable default), the dsp
examples (`wp_DSPExample`, Serve/Client/MapServer/MapClient/Muxer),
higher-order, search-replace, workq, etcd_session, elimination_stack,
lock — ~55 wp lemmas total, 0-1 Admitted. Explicitly unverified
variants exist (`cv_unverified.go`, `muxer_unverified.go`,
`leaky_buffer_unverified.go` — Cond is the recurring reason).
[ANALYSIS] This list is the natural witness-target set for the T3/T4/T7
successor arc: when the spawning frame-quantified `GoSpecC` and the
channel law family land, "we can state and discharge GoSpecC instances
for their verified channel examples" is the parity claim to aim at,
program by program.
