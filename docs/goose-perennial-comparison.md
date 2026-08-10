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
    mit-pdos/perennial (goose README), so this branch is effectively
    FROZEN — perennial is the only live drift surface (per-review
    check asymmetry recorded at the arc-final audit, F26).
  - `deps/perennial` @ `43d4efabc22eb148eb239ebee89d1dd2ee54c900`
    (master; cited `@43d4efa`).
  - **Drift-check record** (owed per review; the arc-final audit's
    check, F26, 2026-08-08): goose `refs/heads/new` upstream =
    `3be88bb…` — UNCHANGED, still the pin; perennial `origin/master`
    has moved to `8d5165bf…`, past the pin (expected, not an error;
    a rev bump is a deliberate recorded event).
  - Cite-resolution caveat (F26): the blanket "all their-side cites
    below are at these revs" has ONE deliberate exception — O1's
    `eb748d43e` is a HISTORICAL off-pin cite (the 2026-01-30
    semantics-deletion commit, "Start deleting old files", verified
    upstream via the GitHub API) unresolvable in our depth-1 shallow
    checkouts; verify it off-checkout per this contract's own rule.
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
| Unbuffered rendezvous | offer protocol channel.go:66-92,151-172 | pairing step, direct handoff (goroutines/rendezvous-hb). SCOPE (audit F11): the cited offer-protocol ranges are exactly what gives THEM select↔select rendezvous, which WE refuse — see the T12b gap row; parity here is op↔op and op↔select only |
| close semantics: drain then zero/`ok=false` | channel.go:135-144 | channels/{closed-receive,range-closed}, close-edge/drain-zero-after-close |
| close panics: send-on-closed / close-of-closed / close-of-nil, gc's exact strings | channel.go:49-50,209-210,229-231; differentially pinned vs real chans channel_test.go:447-622@3be88bb | same strings as `runtimeErrorValue` payloads (slice-1 L9 narrowing); channels/{send-closed-panic,close-closed-panic,close-nil-panic} |
| nil channel: send/recv block forever; len/cap = 0 | channel.go:106-110,190-193,253,267 | nil ops → blocked config → deadlock terminal (channels/nil-values); len/cap 0 |
| select: send cases, recv cases (bare, `v = <-ch`, `v, ok := <-ch`, arbitrary lvalues), default, any arity, `select {}` | translation goose.go:1780-1893@3be88bb; semantics defn/chan.v:40-62,95-114@43d4efa; surface demo testdata/examples/unittest/chan.go:25-57 | SelectClauseHead machinery, entry-time operands, machineSelectTargets lvalue delivery (channels/select-*; scoping/select-clause-scope) |
| select entry-time operand evaluation — OURS ONLY; row corrected at the arc-final audit (F12, 2026-08-08): this row previously asserted PARITY, but goose DIVERGES from gc/spec here — its select translation binds `$v_i` OUTSIDE `$ch_i` for a send clause (goose.go:1874-1889@3be88bb; emitted order `$ch0,$ch1,$v2,$ch2,...` in unittest.v:799-804), evaluating the send VALUE before its CHANNEL, the reverse of spec §Select ("channel and right-hand-side expressions ... evaluated exactly once, in source order"; probed on gc: channel before value). The old hedge cited goose.go:1901's "XXX: left-to-right" caveat — which lives in sendStmt, a DIFFERENT site that goose gets RIGHT ($chan outside $v, unittest.v:756-758): a caveat borrowed from a correct site to hedge an incorrect, unflagged one. Their-side-unfaithful, the §3 class | goose: spec-divergent, unflagged at the site | selectOpsK, spec step 1 (channel-operands-eval-order pins; receive-vs-call lexical-order work, slice-1 log) |
| nonblocking ops never rendezvous with each other | no-offer asymmetry channel.go:90,173; pinned by Test2NBSelectNoProgress channel_test.go:1170-1207 | select-with-default sees parked partners but two defaults never pair (sched-dependent/select-default-handshake, membership-pinned {7,99}) |
| select on closed channels: recv ready with zero/false; send-clause commit panics | clause readiness incl. closed via the model | S2-convergence closed-arrival guard; goroutines/select-closed-arrival/{send,recv-parked-sender} |
| range-over-channel = receive-until-closed-and-drained | `Iter()` channel.go:274-292 + `chan.for_range` defn/chan.v:13-22 | decodeRange `"chan"` desugar (channels/range-closed, range-edge) |
| directional channel types | types.go:586-598@3be88bb | channels/{directional-types,make-directional,close-send-only} |
| `go f(args)`: callee+args evaluated in the spawner | goose.go:1654-1673 | spawn positions; spawn-edge pins |
| close during unbuffered handshake waits for the exchange | tryClose retry channel.go:203-219 | arrival-never-pairs-across-close invariant clause (iv), S2 convergence record |

## 2. They have, we lack

Last-reviewed: channels arc, 2026-08-07 (seeding); rows T1/T3/T7/T10
updated at the spec-parity arc close, 2026-08-10.

| # | What | Their evidence | Our status | Class |
|---|---|---|---|---|
| T1 | `sync` package: Mutex/RWMutex/WaitGroup/Once/sema specs proved over the goose-translated REAL stdlib source, atop a small trusted core (Mutex→CmpXchg spinlock, semaphore model; Cond notifyList STUBBED no-ops) | `new/trusted_code/sync.v:8-58@43d4efa`; `new/proof/sync.v` + `sync_proof/*` (9 files, ~35 wp lemmas) | MACHINE HALF LANDED (spec-parity S2, 2026-08-09, via exactly the recorded growth contract — each primitive one registry entry, ZERO new Choices sites): Mutex/RWMutex/WaitGroup/Once as machine primitives (value-semantics cells, blocked-shape wake, the probed-fatal misuse class, HB edges per the package-doc sentences with the two-clock RWMutex realization). Lane state MEASURED at the arc tip (tracked baseline, `awk -F'\t' '$2~/^sync\//{n++;c[$1]++} END{print n,c["PASS"],c["FAIL"]}' baselines/native-full.tsv` → 35 29 6, plus race/{free,negative}-sync 7/7 PASS): **42 rows — 36 green, 6 PERMANENT fail-closed frontend-export markers**: the FOUR sync/escapes escape-refusals (S2 audit fix round, design note F4) + the Cond/TryLock out-of-scope pair (charter D4). (Correction, S5 audit: this cell first carried the S2 build-slice figure "33 guardrail pins green + 2 permanent markers", which was true pre-audit-round but names 2 of the 6 permanent refusals standing at tip.) The four sync-only goose files R1-green (`docs/2026-08-09_sync-package-design.md` §§11-12). NO sync spec/law layer yet — no sync WP laws, no proved sync specs (the feature-class exemplar is P-S2-3's candidate-when-reached; the arc's proof slices did not reach sync) | **CAP, narrowed** — the machine half is paid; owed: the sync spec layer (P-S2-3) and, for TryLock/atomics, the atomics arc |
| T2 | `sync/atomic`: machine atomics (`LoadOp/AtomicSwap/AtomicAdd/CmpXchg`, lang.v:84-105,1372-1431@43d4efa) + 49 wp lemmas (`new/proof/sync/atomic.v`, their largest single proof file) | ibid. | Nothing; D5 records atomics as the `FairStream` prerequisite arc | **CAP** — owed: atomics arc (FairStream prerequisite) |
| T3 | Logically-atomic channel-op spec set: `send_au/recv_au/close_au` + nested AUs + two incomparable nonblocking variants; proved `wp_NewChannel/wp_Send/wp_Receive/wp_Close/wp_TrySend/wp_TryReceive/wp_Len/wp_Cap` | `chan_au_base.v:106-297@43d4efa` (canonical-weakest-spec problem documented at :244-263); `chan_au_{new,send,recv}.v` | STILL ZERO channel WP/lifting laws — but the seam they land on now EXISTS (spec-parity S4): the decomposition pipe `proofs/GoLeanProofs/LangD.lean` (`StepDC`, the pairing simulation `stepM_erasedD`, run erasure, THE EXIT `goTripleC_of_wpD`, the `wpD_*` kit) is the recorded consumer boundary for the channel WP law family + protocol layer (P-S4-2). Concurrent Iris layer otherwise unchanged (`wpC_fork`/`wpC_pure_det`/`wpC_spawned_strip`, LangC); channel facts still export as kernel certificates / operational predicates (§7.2) | **CAP** (owed WITH its consumer: P-S4-2, the curated rows' D1 form) |
| T4 | Select WP specs: `wp_select_blocking` (`[∧ list]` per-case AUs), `wp_select_nonblocking`, `wp_select_nonblocking_alt` (∗-separated with not-ready witnesses → provable-unreachable default) | `theory/chan.v:272-299,427-455,584-619@43d4efa`; unreachable-default demo `wp_select_nb_guaranteed_ready`, channel_select_tricky_examples.v:117 | None (same deferral as T3) | **CAP** (with T3) |
| T5 | Channel idiom spec libraries: bag, broadcast, contrib (Actris ghost theory), future, handshake, lock, mpmc (1022 ln), spsc (668 ln) | `theory/chan/idioms/*@43d4efa` | None. [ANALYSIS] their idiom set is a map of raft's channel patterns — broadcast/done-channel and bag are what `v3_proof/protocol.v` imports | **CAP** (successor-arc, after T3) |
| T6 | dsp/ — Actris dependent separation protocols over PAIRS of Go channels, with proofmode tactics (`wp_recv`/`wp_send`) and the COFE model in-tree | `theory/chan/idioms/dsp/{dsp,dsp_ghost_theory,proto_model,dsp_proofmode}.v@43d4efa`; example `wp_DSPExample` channel_dsp.v:35 | None (the "Actris-lite" layer named in D8 was deliberately not built in slice 5) | **CAP** (lowest urgency of the spec-layer family) |
| T7 | Frame-quantified WP proofs over genuinely-spawning programs (their entire proof portfolio is this) | e.g. `wp_simple_join` channel.v:259, all of §5's examples | THE TRIPLE HALF IS PAID (spec-parity S4): the recorded obstruction (pool `StepM` pairing touches two threads; iris-lean `Language` steps one) is discharged by the pairing decomposition (`LangD.lean`), and `spawnNoopTripleC` is the first frame-quantified `GoTripleC` at full `InitialSplit` strength on a genuinely spawning program (witness pair `spawnNoopReadoutC` + `spawnNoopTerminatesNormallyC`). Still owed: the safety half (`ProgressExecC` ∀-heap, P-S4-1) to assemble `spawnNoopSpecC`, and WP laws at channel positions (P-S4-2) before any of THEIR portfolio's shapes is reproducible | **CAP, narrowed** — their portfolio-wide practice vs our first instance; owed: P-S4-1 + P-S4-2 |
| T8 | Prophecy variables (HeapLang-inherited; used at scale in vMVCC) | lang.v:244-245@43d4efa | None; slice-5 log records "no prophecies needed — primitive channels make lifting laws the atomic specs" | **DEL** for channels; revisit trigger: a future target needing future-dependent linearization |
| T9 | Crash semantics + FFI worlds (disk, async_disk, filesys, grove network) and the storage-systems portfolio | lang.v FFI parameter; `testdata/examples/{append_log,wal,simpledb,...}` | Out of scope: our north star (etcd-io/raft, the library) needs no disk/net FFI | **DEL** — revisit trigger: a target change |
| T10 | Translated Go stdlib surface: sync, atomic, time, strings, bytes, sort/slices (real stdlib pdqSort proved), context, fmt, encoding/binary, errors, io, log, math… | `etc/ci-goose-check.py:23-41@43d4efa` pins the source repos; `new/code/*`; ~60 stdlib wp lemmas + ~25 slices/sort | Our frontend refuses imports (`tools/nativefrontend/emit.go:4258,4301` — imported named types/methods fail closed; line numbers re-measured at the arc tip at the S5 audit — the seeded `4105,4148` had drifted 153 lines under them), with ONE carve-out since spec-parity S2: the `sync` surface (Mutex/RWMutex/WaitGroup/Once) lowers, and the import pipeline gained the explicit `--allow-import` vet seam (the four sync-only goose files landed R1-green) | **CAP** long-term; scoping Part B quantifies which corpus files this blocks |
| T11 | North-star proof progress: in-progress etcd-raft + etcd verification (`wp_Node__Propose` Qed; etcd client 39 wp lemmas but 29 Admitted; readonly.v 955 ln, 5 Admitted) | `new/proof/go_etcd_io/raft/v3.v:17-29`, `v3_proof/*`, `etcd/client/*@43d4efa`; Go sources external: github.com/upamanyus/{etcd-raft,etcd} branch `goose` | Our quorum pilot is a raft fragment; no raft-package-scale work yet | **CAP** (this is the race; their surface is demonstrably WIP — 51 Admitted across new/proof's 376 wp lemmas) |
| T12b | Select-with-select rendezvous (added at the arc-final audit, F11 2026-08-08 — a real they-have/we-lack gap the seeding missed while §1's rendezvous row implied parity): their blocking select's clauses call TrySend/TryReceive with blocking=true, posting/accepting offers (channel.go:66-92,151-172@3be88bb; chan_au_base chan.v:105-114 `chan_select_blocking` threads blocking into the clauses), and TestSelfSelect runs two concurrent BlockingSelect2 on one unbuffered channel (channel_test.go:848-891@3be88bb) | goose model + test, perennial defn | We REFUSE fail-closed (`select-with-select rendezvous (unmodeled this slice)`, Multi.lean; and over-broadly — any arriving select with a parked-select partner on ANY clause refuses even when another clause is cell-ready, audit F10). Corpus red markers channels/select-select/{core,beside-loop}; owner: the successor select slice (first step: per-clause refusal narrowing in `ArrivalOutcome`, then the offer-protocol rendezvous) | **CAP** on our side |
| T12 | Sub-step interleaving granularity + operational race-UB by construction (two-step na accesses, `naMode Reading n | Writing`; racy access → stuck) | lang.v:543-546,1352-1396@43d4efa | We rejected naMode (grows by revision, D2+D3); registry-granularity + the NPDRF reduction OBLIGATION, whose statement is currently a REFUTABLE-as-written draft (NPDRF.lean; S3 audit) | **DEL** with an honest open metatheory debt on our side — their granularity story is complete by construction; ours rests on the unproven reduction |

## 3. We have, they lack

Last-reviewed: channels arc, 2026-08-07 (seeding).

| # | What | Our evidence | Their status | Class |
|---|---|---|---|---|
| O1 | An executable semantics at all + `go run` differential validation (1194 exec + 311 negative cases, six-lane taxonomy, tracked baseline, zero-drift gates) | design note D9; `baselines/native-full.tsv` | Their GooseLang interpreter + semantics corpus was DELETED with the old semantics (perennial `eb748d43e`, 2026-01-30); the new semantics has NO interpreter and no differential harness (research note §5; `cmd/test_gen -coq` still references the absent `Perennial.goose_lang.interpreter`) | **DEL** on their part (casualty of the rewrite); our differentiator |
| O2 | Channel-model validation IN the trusted semantics: our interpreter IS the model under differential test. Their Go-model tests are real and good (spec-sentence-keyed `channel_spec_test.go:15-98@3be88bb`; runtime-derived + in-process model-vs-native differential `channel_test.go:210-310,447-622`; the `model/go_channel` native twin re-running the identical corpus) but validate the GO model — the model↔GooseLang correspondence and select-model↔`try_select`-axioms are TRUSTED, stated in their own header (select.go:3-5@3be88bb) | — | trust gap on their side | our structural advantage |
| O3 | Deadlock as an observable terminal matching gc ("all goroutines are asleep - deadlock!", exit 2), differentially tested (`expected_status: deadlock`) | slice-1/2 logs; channels/deadlock, goroutines/deadlock | Impossible: blocked = spin loops; a deadlocked program just diverges. No counterpart of Go's runtime detector | **CAP** on their side |
| O4 | In-machine race DETECTION: segment-HB vector clocks (TSan/FastTrack skeleton), HB edges quoted against go_mem at implementation sites, `raceDetected` terminal, racy lane "every enumerated path refuses" + `go run -race` (exit 66) as justifying oracle; DRF-SC boundary pinned executably (sb-chan {1,10,11}, 00 mechanically excluded) | slice-3/4 logs; `GoLean/GoCore/Race.lean` inventory | naMode makes races UB/stuck for PROOFS but is untestable — "Goose has no way to test its race semantics at all" (research note §4); no -race oracle use anywhere | **CAP** on their side |
| O5 | Recoverable channel panics: send-on-closed/close-of-closed/close-of-nil/make-negative are real Go panics — `recover()` works, messages differentially compared | RECOVERABILITY: channels/close-edge/recover-* (all green; they pin non-nil-ness — the recovered value is a runtime error, not a string, so no message text is read there). MESSAGE comparison: channels/{send-closed-panic,close-closed-panic,close-nil-panic} + channels/make-edge/negative-buffer-panic (expected_reason containment at the harness; evidence pointer corrected at the arc-final audit, F24 — the original cell cited the recover-* ids for the message clause they do not test) | In the logic these are `False` branches in `send_au`/`close_au` (chan_au_base.v:205,295@43d4efa) — verified code must prove them impossible; `go.panic` has no proof rules found; the Go-model panics are unreachable-by-obligation. Go defines these as catchable panics | **DEL** on their side (proof-obligation style); faithfulness + testability win on ours |
| O6 | Select multi-ready with a CERTIFIED possibilistic record: L2 envelope statement at the site, membership lane with machine-enumerated observation sets + `members=n` cardinality pins, plain AND -race dual go-run sampling | slice-4 log; channels/select-multi-ready/observable {101,210}, select-wake-multi {1,2}, select-arrival-multi {10,20} | Nondeterminism exists (demonic permutation) but is unexplored: no schedule enumeration, no set certification; select liveness/fairness only EMPIRICALLY tested in Go with sleeps (TestSelectLiveness*, channel_test.go:897-1018@3be88bb) — properties their logic does not state | **CAP** on their side |
| O7 | The sequential-conservation theorem (`execProg_single_eq_execStmt`): every sequential result in the transferable classes is the pool result verbatim — 33 sequential designated statements transfer unrestated; corpus bit-identity as the empirical twin | slice-2 log, `MultiSound.lean` | No analogue needed (no sequential machine) — but nothing plays this role of a machine-level growth-by-extension guarantee | ours-specific asset |
| O8 | ∀-schedule KERNEL certificates + a concurrent termination notion: `forkJoinAllSchedules42/NoDeadlock/NoRace`, `TerminatesNormallyC` (one fuel bound, every stream, main-normal) — designated statements | `proofs/Audit.lean`; `MultiStreams.lean` | Partial correctness only; explicitly no termination/liveness/fairness claims anywhere (research note §3; enumeration §5) | **CAP** on their side |
| O9 | Faithful main-exit — CORRECTED at the arc-final audit (F2, major, 2026-08-08): as originally seeded this row overclaimed. Our pre-BUG-044 model resolved main's exit DETERMINISTICALLY for main (woken goroutines discarded on every stream), excluding members gc realizes — too NARROW, the theorem-transfer-breaking direction, exhibited by the verifier on the plain oracle. Since the L5 main-exit window (BUG-044 fix) the model races main's exit against runnable goroutines like gc, bounded by the exit pick | D6 (amended); BUG-044; goroutines/wake-window/* (membership, statuses=ok+panic); goroutines/main-exit | Pool never removes threads — a safety-conservative SUPERSET (research note §3): sound for them, observationally unfaithful in the too-WIDE direction | **LAT** (their too-wide is free under safety-only; ours is now oracle-validated in both directions at this boundary) |
| O10 | Nil channels inside select | channels/select-nil-default (green) | NOT modeled: their model's `TrySend/TryReceive` have no nil check (channel.go:46-98,120-181@3be88bb — only Send/Receive/Close/Len/Cap check nil); a nil clause would nil-deref in the Go model and is unprovable in Coq (`is_chan` requires `ch ≠ chan.nil`, chan_au_base.v:449); no test covers it | **CAP** on their side |
| O11 | Blocked-config machine states (no spin): O(1) blocking, fuel-friendly, wake as explicit pairing, waiter-queue-priority arrival matching gc's recvq-before-buffer discipline with the re-argued hchan invariant | S2 audit-response redesign (`arrivalPlan`) | Spin loops + mutex; buffered channels post NO offers, so gc's direct-handoff observation (len 0 beside a parked receiver) is not enforced — their model can expose len-transients real gc avoids; they explicitly punt on len reasoning ("might not be worth specifying", channel.go:250-251@3be88bb) | **LAT** — their envelope is wider than gc with no oracle; exactly the class our S2 audit fixed on our side |
| O12 | Statement-TCB discipline: first-order designated statements over the interpreter, comparator-judge independent kernel replay, non-vacuity discharge witnesses per law | CLAUDE.md doctrine; Audit.lean gate | Client-facing channel reasoning is irreducibly higher-order Iris (nested-mask AUs, saved-prop offer parking); no analogue of statement-TCB review or witness gating (their `False`-branch AUs are the vacuity smell our gate exists for, though theirs are deliberate) | **DEL** difference of doctrine |
| O13 | Adversarial-input validation at scale: grossmith fuzzer campaigns (2,900 cases, zero divergences) — measured at `458386d` (the maint-check commit, BEFORE slices 5-6; provenance corrected at the arc-final audit, F25: the original row said "vs the channels-arc tip", one hop stronger than what was executed). Substance holds at the audited tip: the post-`458386d` diff touches no interpreter or frontend executable (proof-layer + docs + one corpus case only — verifier-read) | `docs/2026-08-07_grossmith-campaign.md` (pins the SHA) | No fuzzing of translation or semantics found | ours-specific asset |

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
| L5 | Main exit | Superset (threads keep stepping) | The L5 main-exit window (BUG-044, audit F2): main's terminal opens a bound-2 site while other goroutines are runnable — exit now, or one more pool step — so woken-goroutine continuations gc realizes are in the envelope; "faithful termination" as originally written was too narrow | see O9 |
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

Arc-end note (spec-parity close, 2026-08-10): the spec-parity arc
ENGAGED this list — the select-tricky trio, muxer `client`, and the
dsp example now carry kernel-checked ∀-schedule families beside their
upstream Qeds (per-statement rows in §7.2; per-row gap: the
frame-quantified `GoSpecC`, blocked on P-S4-1/P-S4-2 exactly as this
section's [ANALYSIS] anticipated). §7.4 counts the rest of the
73-item tree by reason (figure corrected at the S5 audit — the
first form said 60, a filename-glob undercount that dropped
elimination_stack.v and lock.v, two members of THIS section's list).

## 6. Imported-corpus status (goose-parity buildout lane)

Last-reviewed: goose-parity end-of-buildout, 2026-08-08
(docs/2026-08-08_goose-parity-end-of-buildout.md is the closing
report); arc-end addendum below added at the spec-parity close,
2026-08-10. The
`Corpus/coverage/exec/imported-goose/` lane (provenance-tagged, verbatim
bodies, goose @ 3be88bb — pipeline `scripts/import-goose`, charter
`docs/2026-08-07_goose-parity-charter.md`) is populating; this section
tracks the phase-1 "verify them all" claim per batch. Their comparable
artifact is the `test_gen` boolean-oracle suite (112 oracles; 36 stated
as `test_fun_ok` Iris lemmas of which **28 proved** — 7 `Abort`, 1
`Admitted`. Count corrected 2026-08-10 at the spec-parity S3 audit:
this line originally said "37 proved", which counted lemma statements
— incl. the Aborts, the Admitted, and the non-`test_fun_ok`
`wp_shouldPanic` — as proved; measured at 43d4efa, correction of
record in `docs/2026-08-07_goose-comparative-scoping.md` B.1. Per-row
status for nil.v — 3 `Qed` / 3 `Abort` — and the R3 standing are in
`docs/spec-parity-r3-manifest.md`).

| batch | units | rows | R1 PASS | R1 FAIL (all recorded fail-closed classes) | R2 kernel pins |
|---|---|---|---|---|---|
| 1 (semantics: scalar ops & control flow) | 10 | 48 | 40 | 8 (call-in-short-circuit-operand quarantine) | 1 pilot (semantics/block: ∀-streams Terminates + readout) |
| 2 (semantics: functions / closures / allocation) | 10 | 22 | 19 | 3 (short-circuit-operand; copy-in-statement-position; map-element multi-assign target — all existing emit.go unsup sites) | 2 (semantics/defer, both oracles) |
| 3 (semantics: data structures) | 8 | 43 | 37 | 6 (all short-circuit-operand quarantine) | 6 (semantics/nil, all oracles) |
| 4 (channel tree, authored wrappers + lane classification) | 5 landed (+2 units, 2 rows parked P2) | 9 | 9 | 0 | 0 (concurrent: outside the sequential checker) |
| 5 (storage-clean + generics) | 7 | 7 | 6 | 1 (short-circuit-operand) | 1 (storage/mapliteral) |
| 6 (unittest wrapper lane, first slice) | 11 | 11 | 11 | 0 | 1 (unittest/const) |

FINAL branch totals (updated at the pre-merge audit round,
2026-08-08 — the buildout-end figures predated the user-authorized bug
fixes): 78 units landed / 172 imported rows — 152 R1 PASS, 20
recorded-fail-closed frontend-export, ZERO deliberate reds (the
buildout-time BUG-048 pin flipped green with the fix); 12 oracles R2
kernel-pinned, all six pin terms staleness-guarded
(check-imported-pins, ci 1c5 — the step label at this paragraph's
date; 3a2 after the renumber at 2927085f); 2 units + 2 rows parked (P2,
ruled-parked at the check-in); 2 GoLean bugs surfaced, filed, pinned,
and FIXED on the branch (BUG-047, BUG-048 — the latter also repaired
two long-standing untriaged backlog reds; ratchet 18 → 16). Per-batch
rows below are historical.

Running totals after batch 6: 51 units landed (28 semantics of 29
clean — remaining panic.go; 5 channel + 2 parked; 7 storage/generics;
11 unittest of ~32 remaining), 140 imported rows, 122 R1 PASS, 18
recorded-fail-closed frontend-export; 11 oracles R2 kernel-pinned (vs
their 28 proved `test_fun_ok` oracles, 36 stated, over 112 — figure
corrected 2026-08-10, see §6's header note; R2 count deliberately
held down pending the parked staleness-guard decision P1, not by
capability).

Batch 4/5 parity notes (corrected at the phase-C fix round,
2026-08-08 — the first version claimed two false deltas): our
channel-example coverage now includes machine-CERTIFIED results for
their verified examples wp_DSPExample (=42, confluent), the
select-tricky trio (their proved-unreachable default included), muxer
Async/Client. For the Google example the delta is METHOD, not
coverage: upstream PROVES `wp_Google` (channel_google.v, Qed, 0
Admitted) with a permutation postcondition `xs ≡ₚ google_expected q`
— the same set-membership content — while ours adds machine-certified
REACHABILITY of all 6 arrival orders (envelope completeness their
partial-correctness triple does not state) plus the executable
differential. interfacerecursion and mutualrec are POSITIVE
gold-translated goose examples at the pinned rev (their `// ERROR
cycle in dependencies` comments are vestigial — consumed only by
TestNegativeExamples, which loads a different tree; TestExamples
passes both) — our units are ordinary valid coverage of
interface/mutual-recursion lowering, NOT a parity delta. Their
generic_conversion example is latently panicking Go (probed: "index
out of range [0] with length 0") that their translation-only tests
never execute — that delta stands. Claim-strength
caveat on that comparison (phase-A checkpoint, 2026-08-08), two-sided:
our R2 pins pair ∀-streams outcome-agnostic `Terminates` with a
CANONICAL-STREAM `.normal` readout (weaker than the designated
`TotalReadout` ∀-fuel/∀-choices shape, as each pin's docstring states);
their `test_fun_ok` is Iris partial correctness with no termination
claim at all (row O8).

Arc-end addendum (spec-parity arc close, 2026-08-10): branch totals at
the arc tip — **82 units / 176 imported rows: 156 R1 PASS, 20 recorded
fail-closed frontend-export FAILs, zero deliberate reds** (commands,
each emitting its figure: `find Corpus/coverage/exec/imported-goose
-mindepth 2 -maxdepth 2 -type d | wc -l` → 82; `awk -F'\t'
'$2~/^imported-goose\//{n++;c[$1]++} END{print n,c["PASS"],c["FAIL"]}'
baselines/native-full.tsv` → 176 156 20). **9 units carry staleness-guarded pinned lowerings**
(`scripts/check-imported-pins` PINS registry: block, defer, nil,
mapliteral, const, rune, select-tricky-examples, muxer, actris-example)
→ 73 unpinned (the P-S3-2 lever). Spec-level standing: 6 sequential D1
pairs (R3) + 6 channel ∀-schedule families — the per-example
statement-by-statement comparison is §7 below; per-row dispositions in
`docs/spec-parity-r3-manifest.md`.

Batch-2 parity delta worth a row of its own: goose's two
`failing_test*` semantics oracles (`failing_testFunctionOrdering`,
`failing_testArgumentOrder`, testdata/examples/semantics/
function_ordering.go@3be88bb — evaluation-order programs their
translation is KNOWN to get wrong vs Go: the file's own comment
"Goose has a right-to-left evaluation order for function arguments,
which is incorrect" (function_ordering.go:79-80) and the mechanized
`failing_` convention itself, `Fail Example` on the Rocq side vs
`suite.Equal(true, …)` on the Go side (cmd/test_gen/main.go:134,166).
[Citation corrected at the phase-A checkpoint, 2026-08-08: the first
version of this paragraph cited goose.go:1901 — the sendStmt caveat
this file's §1 select row (F12) had already ruled misattributed]) both
run R1 differential PASS on our side
(`imported-goose/semantics/function-ordering/{failing-function-ordering,
failing-argument-order}`): evaluation-order fidelity where their
translation diverges from gc.

## 7. The per-example spec-parity table (spec-parity arc close, 2026-08-10)

The charter's slice-5 artifact (`docs/2026-08-09_spec-parity-arc-charter.md`
item 5): one row per covered example — their lemma ↔ our internal
triple ↔ our export/readout ↔ strength delta BOTH directions.
**Location choice, recorded**: this table extends the standing matrix
rather than opening a dedicated doc — one canonical comparison home,
already under this file's maintenance contract (rows move in the same
arc that moves their truth; the R3 manifest
`docs/spec-parity-r3-manifest.md` stays the per-program disposition
record, this table the per-STATEMENT comparison).

Ground rules. All upstream statuses at `deps/perennial` @ 43d4efa,
re-measured for this table (`grep -n 'Lemma\|Qed\.\|Abort\.\|Admitted'
<file>` in `new/proof/github_com/mit_pdos/perennial/goose/testdata/
examples[/semantics_proof]`); denominators re-measured: **36
`test_fun_ok` statements — 28 `Qed` + 7 `Abort` + 1 `Admitted`**; the
semantics_proof directory's Qed total is 29, the extra being the
non-oracle `wp_shouldPanic` (commands in the manifest header, re-run
at arc close, matching; figures restated at the S5 audit so the four
numbers and the denominator visibly sum — the first form juxtaposed
36/29/7/1, which does not partition). **No ordering claim is made
between the two sides' judgments anywhere** (the slice-3/4 discipline):
no relation between GooseLang WPs and our judgments is defined, so
every delta is an itemized difference, not a ranking. Our-side axiom
budget throughout: `[propext, Classical.choice, Quot.sound]`, checked
by the in-build Audit sweep; nothing in this table is designated unless
the D3 curation says so.

### 7.1 Feature class 1 — sequential boolean oracles (the `test_fun_ok` class)

Shared statement forms (fixed by the slice-3 exemplar,
`docs/2026-08-10_wp-walk-driver.md` §1; all six rows instantiate them
over the unit's staleness-guarded pinned lowering, ci step 3a2 —
the step label earlier arc records call "1c5"; it has been 3a2 since
the branch base 2927085f, corrected across the arc docs at the S5
audit):

- **internal triple** — `<name>SpecC : GoSpecC <unit>Lowered.typeDefs.toList
  <unit>Lowered.funcs <unit>Lowered.methods <env> (r ↦ ⟨int, 0⟩) driver
  (r ↦ ⟨int, 1⟩)` at full `InitialSplit` strength
  (sequential-degenerate lane, stated so — these programs spawn
  nothing);
- **export/readout** — `<name>ReadoutC : ∀ fuel ch σf ch', execProg
  fuel <env> <seed> ch driver = .ok (.normal σf, ch') → loadLoc σf
  (.base ⟨0⟩) = .ok (.int 1 .int)` — first-order, pool-carrier,
  deletion-test-clean (no Iris, no relation, no tactic in the
  statement).

Shared strength delta, BOTH directions (the corrected S3-audit
wording, wp-walk-driver §1): THEIR `test_fun_ok` is an unannotated Iris
WP — partial-correctness `NotStuck` over GooseLang, which already
carries no-stuck safety and (GooseLang makes racy accesses stuck)
race-freedom on their model; heap-general and compositional about the
upstream FUNCTION. OURS is grounded in the executable, differentially
tested interpreter (the same `execProg` the `go run` oracle validates),
over the frontend's ACTUAL lowering, with a first-order readout twin
readable from base definitions; driver-level (the wrapper program).
Neither side's judgment here claims termination (our separate
composition `compareNilToNilTerminatesNormally` adds the termination
half on the sequential carrier for the exemplar; P-S3-5 parks the
joint form). Framing is NO delta (their `∀ Φ` WP frames natively).

| example (imported-goose) | their lemma @ 43d4efa | our internal triple | our export | per-row delta |
|---|---|---|---|---|
| semantics/nil `testCompareNilToNil` | `wp_testCompareNilToNil`, nil.v:29, **Qed** :31 | `compareNilToNilSpecC` (`Specs/GooseParityNilWP.lean`) | `compareNilToNilReadoutC`; + `compareNilToNilTerminatesNormally` (R2+R3 composition, sequential carrier) | genuine parity row (both sides prove); shared delta only. Designation CANDIDATE pair (D3) |
| semantics/nil `testCompareSliceToNil` | nil.v:9, **Abort** :20 (their TODO: "need a lemma showing allocations are non-nil") | `compareSliceToNilSpecC` | `compareSliceToNilReadoutC` | our favor at example level: upstream attempted and abandoned; we discharge |
| semantics/nil `testComparePointerToNil` | nil.v:22, **Abort** :27 (TODO: "points-tos are non-null") | `comparePointerToNilSpecC` | `comparePointerToNilReadoutC` | ditto |
| semantics/nil `testComparePointerWrappedToNil` | nil.v:33, **Abort** :38 (TODO: "array points-to is non null") | `comparePointerWrappedToNilSpecC` | `comparePointerWrappedToNilReadoutC` | ditto |
| semantics/nil `testComparePointerWrappedDefaultToNil` | nil.v:40, **Qed** :46 | `comparePointerWrappedDefaultToNilSpecC` | `comparePointerWrappedDefaultToNilReadoutC` | genuine parity row; shared delta only |
| semantics/block `testExplicitBlockStmt` | **no statement** (block has no lemma in semantics_proof/) | `explicitBlockSpecC` (`Specs/GooseParityBlockWP.lean`; + sequential `explicitBlockSpec`) | `explicitBlockReadoutC` | same-class coverage row, not a parity row |

Deltas AGAINST us in this class, named (manifest rows, unchanged at
arc close): `testInterfaceNilWithType` (nil.v:48, **Qed** :50) —
out-of-class at R3, the short-circuit `Expr.and`/`Expr.or` WP law gap;
plus the FOUR frontend-blocked upstream-Qed oracles
(`testStructUpdates` structs.v:9 Qed :11; `testPrimitiveTypesEqual`,
`testDefinedStrTypesEqual`, `testListTypesEqual` type_equality.v:9/13/17
Qed :11/15/19 — all `FAIL frontend-export` in the tracked baseline, the
short-circuit-operand quarantine).

### 7.2 Feature class 3 — the curated channel exemplars

Shared statement family per row (slice 4,
`docs/2026-08-10_gospecc-decomposition.md` §6 option (a);
`Specs/GooseParityChannels.lean`, over the pinned lowerings): FIVE
kernel theorems — `<row>Cert` (the kernel certificate
`allStreamsOkPool post fuel = true`), `<row>AllSchedules` (∀-schedule
verdict readout), `<row>NoDeadlock`, `<row>NoRace`,
`<row>TerminatesNormallyC` — all interpreter-vocabulary. NOT the D1
pair; each row's recorded gap is the frame-quantified `GoSpecC`
(needs the decomposition pipe's consumers + the channel WP law family,
P-S4-1/P-S4-2).

Shared strength delta, BOTH directions (the manifest FC3 paragraph, as
corrected at the S4 audit): THEIRS are heap-general compositional Iris
triples about the upstream functions (protocol/ghost-carrying),
partial-correctness `NotStuck` — no termination and no
deadlock-freedom (blocking is loop-based, so `NotStuck` holds of a
parked-forever schedule); their channel semantics is the goose
translation of a Go model package that IS well tested in Go (incl.
against real channels, upstream CI) — the Rocq/GooseLang model and the
translation step are executed by no test. OURS are seed-concrete (no
frame quantifier — WEAKER in generality), driver-level, and quantify
EVERY modeled schedule of the differentially tested `execProg` with
totality + exact verdict + deadlock- and race-refusal-freedom —
classes their logic does not state (rows O3/O6/O8).

| corpus row (imported-goose/channel/) | their lemma @ 43d4efa | our theorems (namespace, verdict) | per-row note |
|---|---|---|---|
| select-tricky-examples `nb-not-ready` | `wp_select_nb_not_ready`, channel_select_tricky_examples.v:71, **Qed** :114 | `ChannelSelectTricky.nbNotReady{Cert,AllSchedules,NoDeadlock,NoRace,TerminatesNormallyC}`, verdict 1 | parity at ∀-schedule strength; gap: frame-quantified GoSpecC |
| select-tricky-examples `nb-guaranteed-ready` | :117, **Qed** :137 (incl. their proved-unreachable default) | `…nbGuaranteedReady*`, verdict 1 | spawns nothing — the sequential-lane triple is ALSO blocked (sequential channel WP laws, §6(c) declined with reason) |
| select-tricky-examples `nb-full-buffer-not-ready` | :219, **Qed** :258 | `…nbFullBuffer*`, verdict 1 | same gaps as `nb-guaranteed-ready` |
| muxer `async` | **no upstream lemma** for `Async` (searched `channel*.v`; `wp_HelloWorldAsync` is a different function) | `ChannelMuxer.async*`, verdict "async" | coverage row, not a parity row |
| muxer `client` | `wp_Client`, channel_dsp.v:152, **Qed** :172 | `ChannelMuxer.client*`, verdict "Hello, World!" | leaked parked server at main's exit is inside the modeled envelope (D6/L5) |
| actris-example (dsp) | `wp_DSPExample`, channel_dsp.v:35, **Qed** :57 (dependent-separation-protocol session) | `ChannelActris.dsp*`, verdict 42 | flagship row; `dspCert`+`dspAllSchedules` are the class's designation CANDIDATES (D3) |

### 7.3 Golden exemplars with an upstream correspondence (class analogues, not verbatim rows)

Our golden/designated programs are AUTHORED, not imported — where one
corresponds to an upstream example it is a correspondence of feature
CLASS, never a verbatim-body parity row. Rows with no upstream
counterpart (the golden slice `goldenSpecC`/`goldenReturnsTwoC`, the
recover and quorum families, `spawnNoopTripleC`, the golden select-done
probe) are deliberately NOT tabled here.

| ours (designated unless noted) | upstream analogue @ 43d4efa | correspondence + deltas both directions |
|---|---|---|
| the fork/join family — `forkJoinAllSchedules42`, `forkJoinNoDeadlock`, `forkJoinNoRace`, `forkJoinTerminatesNormallyC` (+ stream pins; `Specs/GoldenForkJoin.lean`, designated + Comparator-replayed) | `wp_simple_join`, channel.v:259, **Qed** :287 | class analogue: spawn a worker, join through a channel. Bodies differ (theirs: buffered(1) done-signal + shared string write, examples.go:50; ours: unbuffered send of 42 into the pinned cell). Theirs: heap-general compositional partial-correctness triple. Ours: seeded ∀-schedule totality + exact verdict + no-deadlock/no-race, kernel-certified, designated. No ordering claimed |
| google-search membership certification (corpus `imported-goose/channel/google-search`, `members=6`, `tier=slow`, `cases.tsv`; certified set re-checked complete at exactly six members, S1 record) | `wp_Google`, channel_google.v:165, **Qed** :412 (permutation postcondition `xs ≡ₚ google_expected q`) | the delta is METHOD, not coverage (§6 note): theirs is a proved Iris triple with the set-membership content; ours is machine-CERTIFIED reachability of all 6 arrival orders (envelope completeness their partial-correctness triple does not state) + the executable differential. NO Lean theorem on our side for this unit (its THREE-worker fan-in — a 4-thread, width-4 schedule tree; enum-stats: ~40.0M steps, 59601 leaves, maxdepth 15 — is past the kernel checker's cost envelope, P-S4-5; descriptor corrected at the S5 audit: three docs carried "5-worker", contradicting the row's own 3! = 6 arrival orders) |

### 7.4 Population, both directions

**What upstream has that we do not attempt (or cannot yet), counted by
reason.**

- *Sequential `test_fun_ok` class* (36 statements, 28 proved): our
  theorems cover 5 of the 36 (2 their-Qed + 3 their-Abort). Of the
  remaining 31: **1 out-of-class at R3** (`testInterfaceNilWithType` —
  the short-circuit law gap), **4 frontend-blocked at R1** (all
  upstream-Qed; the short-circuit-operand quarantine), **26
  no-pinned-lowering** (21 of them upstream-Qed; R1-green rows exist,
  the lowering terms were never pinned — the P-S3-2 import-tooling
  lever, a policy call, not a proof gap). Class-2 units (const, rune,
  mapliteral) and the defer oracles have NO upstream `test_fun_ok`
  statements and are our not-attempted coverage backlog (manifest,
  reasons recorded).
- *Channel-examples proof tree* — **73 Lemma/Theorem items, all
  Qed-closed** (CORRECTED at the S5 records audit: the first form of
  this bullet, and the S4 manifest paragraph it inherited from, said
  60, derived from a FILENAME glob — `channel*.v` plus the two named
  subdirectory files — that silently dropped `elimination_stack.v`
  (8 items) and `lock.v` (5), both members of §5's own enumeration of
  their verified set; an 18% undercount of the against-us population,
  a glob artifact in the self-favorable direction, not a recorded
  scope. The corrected set is DIRECTORY-derived — every proof file in
  `semantics_proof/`'s parent `examples/` dir whose imports reference
  the `testdata.examples.channel` package family — and the command
  emits the figure: `grep -hE '^(Lemma|Theorem)' $(grep -l
  'testdata\.examples\.channel' *.v channel/*.v) | wc -l` = **73**;
  per-file: channel.v 12, dsp 9, google 9, select-tricky 10,
  fibonacci 5, higher-order 3, search-replace 3, workq 4,
  etcd_session 5, elimination_stack 8, lock 5; zero
  `Abort.`/`Admitted.` across all of them). Our curated set
  discharges ∀-schedule families beside **5** of the 73 (the three
  trio lemmas + `wp_Client` + `wp_DSPExample`). The remaining 68 by
  reason: **10 P2-parked** (fibonacci 5 + higher-order 3 — the
  recorded import-enumeration parking; muxer `client-old`/
  `make-greeting`'s `wp_MapClient` channel_dsp.v:271 Qed :313 +
  `wp_makeGreeting` :358 Qed :385 — P-S4-3); **9 beyond the checker's
  cost envelope** (channel_google.v — the unit IS imported, R1-green,
  membership-certified; §7.3's row records the method delta; P-S4-5);
  **34 not imported** (channel.v 12 + workq 4 + etcd_session 5 +
  elimination_stack 8 + lock 5 — upstream units outside the imported
  corpus; `wp_simple_join` is class-analogued by §7.3's fork/join
  row); **15 imported but unattempted at spec level** (select-tricky's
  other 7 — ghost-state/atomic-update HELPER lemmas for its same
  three programs, all three of which §7.2 attempts; no ≥2-ready
  select example exists in that unit, and checker L2 branching stays
  a conditional-FUTURE need per the S4 note §6(c), not a current
  blocker — dsp's other 5, search-replace's 3 incl. its main
  `wp_SearchReplace`: items in R1-green imported units, item ≠
  corpus row (parallel-search-replace has ONE row beside its three
  proof items), no certificates written; visible manifest population,
  not silent skips. Clause rewritten at the S5 audit — the first form
  called the helpers "examples" and attributed a ≥2-ready blocker
  that does not exist upstream). NOTE the number collision: the
  73-item UPSTREAM tree here is unrelated to OUR 73 unpinned imported
  units (§6 addendum) — same numeral, different populations.

**What we prove/validate that they do not.**

- The **3 upstream-Abort discharges** (§7.1 rows 2–4): oracles they
  attempted and abandoned, with their own TODOs naming the missing
  lemmas.
- **2 coverage rows with no upstream statement** (semantics/block,
  muxer async).
- Per-row on all six channel exemplars: ∀-modeled-schedule TOTALITY +
  exact verdict + no-deadlock + no-race (their logic states no
  termination/liveness/deadlock-freedom — rows O3/O6/O8).
- **Explicitly-unverified upstream variants run differentially green
  here**: muxer-unverified/{done,drained} (upstream
  `muxer_unverified.go`, Cond the recorded reason) and
  parallel-search-replace — R1 PASS rows.
- **Their known-wrong translation rows**: goose's two `failing_test*`
  evaluation-order oracles run R1 differential PASS here (§6 batch-2
  note) — fidelity where their translation is documented incorrect
  vs gc.
- The whole imported set is EXECUTED against `go run` THROUGH THE
  VERIFICATION SUBJECT — the differential runs the same `execProg`
  the theorems quantify (176 rows, 156 PASS, the rest recorded
  fail-closed). Stated precisely BOTH directions (CORRECTED at the S5
  records audit — the first form said "upstream's example tests are
  translation-golden only", which is FALSE and re-introduced,
  generalized, the pre-S4-correction one-sidedness this same file's
  §7.2 already fixes): upstream DOES execute its example programs in
  Go — the semantics oracles run as a 115-assertion testify suite
  (`testdata/examples/semantics/generated_test.go` — incl.
  `TestCompareNilToNil` :279 and the four §7.1 frontend-blocked
  oracles :403/:455) and the channel examples have seven executing
  `_test.go` files (`examples_test.go`'s `TestDSPExample` asserts
  42), both run in upstream CI (`.github/workflows/build.yml:33-34`,
  `go test ./testdata/examples/...`); the unittest/storage/generics
  trees have NO executing tests (no `_test.go` there — measured), so
  translation-golden-only is true of THOSE trees alone. The delta
  that stands is rows O1/O2's, about the verification subject:
  nothing on their side executes the Rocq/GooseLang model or the
  translation step the proofs are ABOUT, while our differential
  exercises the very semantics our theorems quantify.
