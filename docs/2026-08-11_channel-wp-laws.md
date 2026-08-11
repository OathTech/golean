# The channel WP law family (channel-logic arc, slice 1)

Status: DESIGN OF RECORD for the slice, opened before building (the
binding discipline). Charter: `docs/2026-08-10_channel-logic-arc-charter.md`
work-plan item 1; the seam it builds on is spec-parity slice 4's LangD
pipe (`docs/2026-08-10_gospecc-decomposition.md` §§3–4,
`proofs/GoLeanProofs/LangD.lean`). Branch `channel-logic-s1` off
`channel-logic`. FD1–FD9 apply; latitude taken below is LAW-DESIGN
latitude (options + recommendation, decided here and recorded).

Everything in this slice is proofs-side (FD6): no machine change, no
new `Choices` site, no envelope change, zero corpus effect. The
certificates (fork/join family, the six curated rows) are untouched
validation anchors; the logic lands beside them.

## 1. The setting: what a channel op looks like on the D-carrier

The laws are stated against `StepDC` / `PoolCfgD` (`LangD.lean`) — the
decomposed per-thread Language whose exit (`goTripleC_of_wpD`)
produces frame-quantified `GoTripleC`s. The relevant facts, measured
from the code:

- A channel statement reaches its APPLY POSITION as
  `.retV v (.chanStK op done [] env k)` (`chanSelApplyPos = true`);
  select as `.retV v (.selectOpsK …)`. Everything before (operand
  evaluation) is ordinary sequential stepping.
- From an apply position the D-steps are: the CELL PATH
  (`StepDC.lift` of `Step.chanStApply`/`chanStApplyPanic`, i.e.
  `applyChanOp`: enqueue / dequeue / panic / park) and the PAIRING
  (`StepDC.pairArrive`: the arriving thread takes its `applyPairing`
  projection with the whole state delta; the partner pool is
  ∃-quantified). `selCommit` fires only on a `.multi` analysis, which
  `arrivalCases` produces only for select — never for a chan-op
  (`arrivalCases` on `chanStK` yields `.single`/`.cellPath`).
- From a PARKED shape (`.blockedSend`/`.blockedRecv`/`.blockedSelect`)
  the D-steps are: WAKE (`resumeThread` against the current cell —
  close-panic / drain / closed-zero delivery; `.ok` only when the cell
  is wake-ready) and RELEASE (`StepDC.pairRelease`: the parked side's
  `applyPairing` projection, state-preserving at the CURRENT state,
  with the pairing's pre-state, partner, and delivered value all
  ∃-quantified).
- Delivery entry is state-preserving: `resumeRecvDelivery` /
  `selectRecvDelivery` / `enterRecvTargets` return `(config, s)` with
  `s` unchanged — the delivered value rides IN the successor
  configuration (`recvStores v ok n`), and the actual stores are the
  receiving thread's own later `tgtOpK`/`storeK` steps. Consequently:
  - an arriving SEND's pairing step is pure control (`.next k`, state
    unchanged) whenever the buffer is empty (nonempty refuses
    `.internal` — the hchan breach guard);
  - an arriving RECV's pairing step at an empty buffer is a
    state-preserving delivery of an ∃-quantified value; at a nonempty
    buffer it is the head-and-refill (cell write + delivery of the
    head).

### 1a. The phantom-pairing cost (the wider envelope, stated honestly)

`StepDC.pairArrive`/`pairRelease` quantify the pool existentially —
a per-thread rule cannot see the other threads. So at ANY open-channel
apply position the WP must absorb pairing steps against ADVERSARY
partners that the real program's pool never contains ("phantom
pairings"): a buffered send with room has both the enqueue successor
(cell pushed) and the pairing successor (cell unchanged, value
teleported); a receive absorbs delivery of ANY value. This:

- makes every channel-law continuation DISJUNCTIVE over the outcome
  set (the laws below enumerate it);
- is SOUND-conservative: it can only weaken what is provable, never
  make a false statement provable (the exports quantify `execProg`;
  the simulation direction is unchanged);
- hits even sequential-degenerate programs on the D-carrier (a
  1-thread program's buffered send still has the phantom-pair branch)
  — the recorded reason spec-parity §6(c) declined sequential channel
  laws was to avoid shipping the family twice; this note is the once;
- is the O1(a) cost the decomposition note predicted. The protocol
  layer (slice 2) constrains the DELIVERED VALUE by ghost+invariant
  but does not remove the phantom branches; removing them is the
  O1(b) cell-mediated Language refinement, recorded there as a fresh
  Language wrapper if slice 2 wants it. Slice-1 decision: absorb, do
  not refine (minimal sound envelope; refinement without a consumer
  is scaffold).

## 2. Resource discipline (FD2: native invariant+ghost at the pin)

Two channel-cell disciplines, both shipped as law FORMS:

- **Owned-cell (points-to) form** — for positions where one thread
  owns the channel cell (`a.id ↦ cell` at full fraction; the house
  gen_heap has no fractions, ownership is exclusive). Usable for
  sequential-degenerate walks and for close/len/cap by an owner.
- **Invariant form** — the cross-thread form: the cell lives in an
  Iris invariant (`Iris.inv N Icnt`, pin API `inv_alloc`/`inv_acc`),
  opened around the ONE primitive step (the apply/wake/release is
  atomic — one `StepDC` step), timeless-stripped exactly as the
  sequential house precedent `wp_store_step₂_inv` (Lifting.lean)
  established. The law takes the accessor pair
  `hopen : Icnt ⊢ ∃ cell, ⌜S cell⌝ ∗ a.id ↦ cell` and per-outcome
  close obligations, with `S : HeapCell → Prop` the cell-shape
  predicate the invariant maintains.

Options considered for the cross-thread form:

- (a) **Accessor/invariant style (taken)** — `hopen`/`hclose` against
  a shape predicate `S`; the house precedent exists, the pin needs no
  new machinery, and the exemplar's `S` is a constant cell.
- (b) **HoCAP atomic-update style** (Perennial's `send_au`/`recv_au`
  against a logical `own_chan` state): strictly more compositional,
  but it REQUIRES the logical channel-state ghost (`own_chan`'s
  auth/frag pair) — that ghost is precisely the slice-2 protocol
  layer. Recorded as the slice-2 refinement: when `own_chan` exists,
  restate the laws au-style OVER these accessor laws (derivation, not
  restatement of this slice's laws — they stay as the primitive
  layer).

No new local constructions over the pin's RA library are needed this
slice (FD9 latitude held in reserve): the exemplar's invariant content
is first-order heap data; the protocol ghost is slice 2's.

## 3. The law family, per primitive

House obligations shared by all: `wpD_*` naming; stuckness-generic
(`@ s`; NotStuck reducibility discharged inside from the enumerated
outcome set); axioms classical trio (Iris side, FD7); every law ships
its discharge witness same-commit, Audit-registered (name tripwire);
docstrings state exactly what the witness demonstrates.

Notation below: the send apply is
`.retV v (.chanStK (.send elem) done [] env k)` with operand list
`(v :: done).reverse = [chv, vv]`; recv similarly with `[chv]`. The
laws take `chv = .chan ⟨some (.base a)⟩` as a hypothesis (nil-channel
laws are a separate row, below) and a σ-pinned normalization premise
`hnorm : ∀ σ, pins → normalizeValueForTy σ elem vv = .ok v'`
(the `wpD_fork` `hspawn` idiom — normalization consults only the
pinned `types` in the shapes the witnesses exercise).

**SEND at the apply position (invariant form, `wpD_chan_send_inv`).**
Outcome set (measured from `applyChanOp` + `chanArrivalPlan` +
`applyPairing`):
1. cell closed → `.panicking ["send on closed channel"] k`, state
   unchanged;
2. open, `buf.size < cap` → `.next k`, cell := push (the enqueue);
3. open, full → `.blockedSend (some loc) v' k`, state unchanged (the
   park);
4. open, buf empty (pairing) → `.next k`, state unchanged (phantom or
   real — indistinguishable per-thread, §1a).
Law obligations: one continuation per branch, each under the
reestablished invariant (branch 2 additionally takes an S-preservation
premise for the pushed cell). Branches are REFUTED by `S` where `S`
excludes them (the exemplar's `S` pins `chanData #[] 0 false`: only
3 and 4 survive).

**RECV at the apply position (`wpD_chan_recv_inv`).** Outcome set:
1. buf nonempty → dequeue head, cell := eraseIdx, deliver
   `(head, true)` (delivery-entry config; `.next k` for zero
   targets);
2. buf empty, closed → deliver `(zero, false)`, state unchanged;
3. buf empty, open → `.blockedRecv (some loc) targets elem env k`
   (the park), state unchanged;
4. open pairing at empty buf → deliver `(v, true)` for an
   ∃-QUANTIFIED `v`, state unchanged — the continuation is
   ∀-quantified over the delivered value (§1a; the protocol layer
   ties it in slice 2);
5. open pairing at nonempty buf (head-and-refill) → deliver
   `(head, true)`, cell := rotate-with-∃-tail — only reachable when
   `S` admits a nonempty buffer alongside send-side waiters; the law
   carries the branch with the refilled cell ∃-quantified over the
   partner's value.
Zero-target instantiation collapses every delivery to `.next k`.

**Parked SEND (`wpD_blocked_send_inv`).** From
`.blockedSend (some loc) v' k`:
1. wake, closed → `.panicking ["send on closed channel"] k` (state
   unchanged);
2. wake, room → `.next k`, cell := push;
3. release → `.next k`, state unchanged (the partner completed the
   handoff; ∃-quantified pairing).
Reducibility: at least one branch exists at every S-state PROVIDED the
release construction goes through — constructible when the current
buffer is EMPTY (arm-3 direct handoff at the current state). At a
nonempty (full, cap ≥ 1) buffer the constructive release needs the
storeLoc ROUND-TRIP lemma (rebuild a pre-state whose rotation is the
current state) — exactly the lemma family the decomposition note
scoped to O1(b). SCOPE DECISION: this slice ships the law for the
`S ⊆ {empty-buffer cells}` class (which covers every cap-0/rendezvous
program — a machine-reachable parked sender at cap 0 always sits at an
empty buffer); the buffered parked-sender law is RECORDED owed with
the round-trip lemma as its named prerequisite and the buffered
exemplars (slice 3 rows with buffered parks) as its consumer.

**Parked RECV (`wpD_blocked_recv_inv`).** From
`.blockedRecv (some loc) targets elem env k`:
1. wake, buf nonempty → dequeue+deliver (cell write);
2. wake, closed empty → zero/false delivery, state unchanged;
3. release → delivery of ∃-value `(v, true)`, state unchanged.
Reducibility: empty+open → branch-3 construction (arriving-send
handoff at the current state — needs only the cell's existence, which
the opened invariant supplies); nonempty → branch 1; closed → branch
2. No scope gap.

**CLOSE (`wpD_chan_close` / `_inv`).** The close apply is a `chanStK`
position but `chanArrivalPlan` returns `none` for `.close` — NO
pairing branch (proved by inversion, not assumed). Outcomes: closed →
panic; open → cell := closed:=true. Both forms (owned + invariant)
are cheap; the owned form ships first with the probe witness; the
invariant form is a mechanical sibling recorded if unshipped.

**LEN/CAP.** `len(ch)`/`cap(ch)` are strict-operator applications
(`strictK` positions — NOT `chanSelApplyPos`), so on the D-carrier
they are resource-conditioned READS: the D-port of the sequential
`wp_det_step_keep` core plus the cell (owned or under invariant).
No channel-specific law shape beyond the read.

**MAKE (`wpD_make_chan`).** `makeChan` is a wide-statement apply
(`stmtOpK` — not an apply position, no pairing branch): allocates the
`chanData` cell and stores the handle into the target — exactly the
sequential `wp_alloc_store_step` class; the D-port of that core IS the
law. Fresh-address ∀ discipline unchanged.

**SELECT (designed; SHIPPING DEFERRED to a later tranche of this arc
— parking ledger P-CL1-2).** The select apply position has the richest
outcome set: `applySelectCore` `.done` (default taken / park /
singleton-ready commit), the `.picks` L2 multi-ready commits
(`Step.selectApply` quantifies the stream — any ready clause's commit
is a step), PLUS `selCommit` (∃-analysis `.multi`) and
`pairArrive` per waiter-extended-ready clause. The law shape is the
same disjunctive-continuation pattern with three extra branch
families: per-ready-clause cell commits (∀ clause), per-clause
pairings (∀ clause, ∃ value on recv clauses), and the default/park
when the ready set is empty — the ready set computed from the
S-constrained cell per clause. Nothing about it needs the protocol
layer; it is deferred on BUDGET (it multiplies the inversion kit by
the clause structure) with its intended consumers named: the
select-tricky trio's frame-quantified rows (charter slice 3). Until
then the trio's ∀-schedule certificate family remains their record.

**NIL-CHANNEL ops — and what actually protects against vacuous
triples** (REWRITTEN at the S1 audit fix round, 2026-08-11 — the
original paragraph was the audit's confirmed MAJOR: it claimed nil
parks are irreducible, that no `applyPairing` arm matches a `none`
loc, and that deadlocking programs "cannot get a triple through this
pipe". All three claims were FALSE, proved so by compiled probes now
tracked in `Specs/ChanVacuityWarning.lean`):

- A nil send/recv parks as `.blockedSend/Recv none …` and `wakeReady`
  is never true of it — that much stands. But `applyPairing`'s
  ARRIVING-side patterns are the only ones requiring `some loc`; its
  PARTNER patterns match the partner's channel with a WILDCARD, and
  `isBlockedConfig` does not inspect the channel. So a nil park is
  both SPINNABLE (`nilParkSpins` — the shipped `stepDC_parked_spin`
  applies verbatim) and RELEASABLE to `.next k` (`nilParkReleases`)
  whenever the state holds any empty-buffer channel cell. (A nil-park
  WP LAW along the parked laws' lines is therefore derivable — the
  round-2 verifier compiled one in a scratch probe — but none is
  SHIPPED and the claim is scoped to the tracked step-level witnesses
  above: we do not ship laws without consumers, and the tracked
  fixtures are the negative knowledge the corrected paragraph needs;
  S1 audit round 2.) The only state in
  which a nil park is irreducible is the degenerate one with no
  pairable channel cell anywhere — nothing rests on that case.
- Independently of nil channels (S1 audit round 2 — an earlier
  "Consequently" here linked the two facts falsely: the demonstration
  program parks on a REAL channel nobody sends on and needs no nil
  park at all), **a deadlocking program DOES get a frame-quantified
  triple through this pipe**: `deadlockRecvTripleC`
  (`ChanVacuityWarning.lean`) proves, with the shipped laws and the
  shipped exit at the exemplars' exact axiom set, a `GoTripleC` for a
  program the interpreter classifies `.deadlock`
  (`deadlockRecvDeadlocks`/`deadlockRecvDeadlocksAdv`, kernel-evaluated
  at the canonical and an adversarial stream — the ∀-stream form is
  deliberately NOT claimed: `transferable` excludes `.deadlock` from
  the conservation kit, so it is not mechanical; scope recorded at the
  theorem, S1 audit round 2). This is not a bug:
  `GoTripleC` is RUN-CONDITIONED partial correctness — every premise
  chain starts from `execProg … = .ok (.normal σf, _)` — so it is
  vacuously provable for non-completing programs BY DESIGN.

**The protection story, stated per the TCB-grounding principle (user
doctrine 2026-08-11):** the trusted claim of a channel bundle is
never the triple alone. The trusted claims are BORING, semantically
trivial properties of the interpreter — the ∃-completion member
(`TerminatesNormallyC`-class, discharged by kernel evaluation) and
the run-conditioned readout — and the Iris/Löb/simulation machinery
is untrusted METHOD for producing them. Enforced structurally — and
REBUILT SEMANTIC at audit round 2 (the first, name/glob/module-based
gate was escapable four ways; the round-2 delta review proved each):
the **completion-pin gate** (`Audit.lean`) classifies every
`theorem`/`def` across ALL `GoLeanProofs.Specs.*` modules by the
TYPE's transitive `defnInfo`-unfolding closure (so `GoSpecC` and any
wrapper reach `GoTripleC`), extracts each triple's `prog` argument,
and requires a `TerminatesNormallyC` pin FOR THAT PROGRAM anywhere in
scope (per-PROGRAM pairing; wrapper-hidden triples fail closed; the
pin side stays a shallow scan — recorded: its failure direction is
loud). Every pre-existing `GoSpecC` export gained its genuine
pool-carrier pin at the round (eleven new `*TerminatesNormallyC`
theorems, the sequential completions lifted by conservation —
`terminatesNormallyC_of_terminatesNormally`); the escape shapes are
tracked fixtures (`ZzVacuityGateFixtures`, negative-tested).
`ChanVacuityWarning` — whose program can have no
completion pin, by construction — is the gate's negative-test
fixture (the raw checker must flag it, and it is excluded from
enforcement by exact name with the reason recorded at the gate).

### 3a. The supporting cores (D-ports of Lifting.lean engines)

The channel laws and the exemplar walk need these D-carrier ports of
the sequential lifting cores — each a mechanical re-plumb of the
sequential proof over `GoPrimStepD` with the two extra refutation
side-conditions (`isBlockedConfig c = false`, `chanSelApplyPos c =
false`) discharging the decomposed rules via `stepDC_shape_cases`:

- `wpD_det_step_keep` — resource-conditioned non-mutating step (var
  loads, deref, len/cap reads);
- `wpD_store_step` — deterministic owned-cell store (assign/store
  positions of the walk; close's owned form rides it);
- `wpD_alloc_store_step` — the makeChan/makeMap class;
- `wpD_fork_alloc₁` — THE ALLOCATING FORK: `wpD_fork` covers only the
  state-preserving spawn class (no params); a worker taking the
  channel as a parameter allocates one cell in `spawnStep`
  (`bindParams`). The law hands the child's WP the fresh param cell
  (`∀ pa, pa.id ↦ pcell -∗ …`), `∀`-quantified over the machine's
  address choice — LangC's recorded "gen_heap-update variant lands
  with its first consumer"; this exemplar is that consumer.

## 4. The exemplar (work-plan item 2): choice and route

**Choice: a purpose-built minimal rendezvous, `chanRendezvousProg` —
recorded against the flagship alternative.** The six flagship rows
need the protocol layer for their stated verdicts (delivered-value
content) and their real lowerings walk far more machinery (select,
strings, loops); an honest minimal exemplar that proves the ROUTE
beats a stalled flagship (the brief's own words). The fork/join
GOLDEN program (`forkJoinDriver`) is the shape template but receives
INTO a target cell — with the slice-1 (protocol-less) laws the
delivered value is ∃-quantified, and an ∃-valued store through the
typed target machinery would force the walk through arbitrary-value
store steps. The exemplar therefore uses the ZERO-TARGET receive
(receive-and-discard — a real Go idiom, `<-ch` as a join signal):

- `rdvWorker(ch chan int) { ch <- 42 }` — spawned goroutine;
- main: `go rdvWorker(chv); <-chv` (sequence of `goStmt` +
  zero-target `chanRecv`), with the channel PRE-SEEDED in the initial
  heap (handle cell + `chanData #[] 0 false` cell) and reached
  through `env₀` — makeChan deliberately NOT in the exemplar walk
  (the parenthetical that stood here — "its law is witnessed
  separately by the sequential-degenerate probe below" — went STALE:
  neither the makeChan law nor `chanOpsProbe` shipped; see P-CL1-6,
  the honest disposition, and the S1 audit fix round); this keeps the
  exemplar's law set exactly the rendezvous four + fork + loads.
- Pre `P` = harness ∗ handle ∗ chanData cells; post `Q` = harness ∗
  handle (the chanData cell is SURRENDERED to the invariant at the
  start of the WP walk and does not return — `GoTripleC`'s Q side is
  intuitionistic; recorded as the standing cost of the invariant
  form: a triple's Q cannot mention cells that were shared. The
  protocol layer's exported readouts will speak about them through
  history predicates instead, per D8.)

**The invariant**: `Icnt = a_ch.id ↦ ⟨chanData #[] 0 false⟩` — a
CONSTANT cell: at cap 0 with nobody closing, every reachable channel
step of both threads is state-preserving (send: park/pair; recv:
park/pair-∃; parked sides: release; wake branches all refuted by the
pinned shape). `S = (· = the cell)`; every `hclose` is trivial.

**The route** (the D1-BOTH pair, charter form):
1. Laws: the §3 rendezvous set + §3a cores, each proved on the
   D-carrier.
2. `wpD_chan_rendezvous_witness`: the full WP walk of
   `chanRendezvousProg` — main's WP (loads, fork via `wpD_fork_alloc₁`,
   strip, recv apply → park → release → stop) and the child's WP
   (frame entry via the fork law, param load, send apply → park →
   release/pair → frame fall → terminal), under the invariant
   allocated by `inv_alloc` from the pre's chanData cell at the walk's
   head. This walk IS the discharge witness for every law it uses.
3. `chanRendezvousTripleC : GoTripleC …` via `goTripleC_of_wpD` — a
   frame-quantified triple whose PROGRAM communicates on a channel
   across goroutines. SCOPED at the S1 audit fix round: the triple
   ALONE does not certify the communication — it is run-conditioned
   and compatible with a never-communicating program
   (`deadlockRecvTripleC`, the warning fixture, is the standing
   demonstration). What separates this bundle from a vacuous one is
   the COMPLETION PIN: `chanRendezvousTerminatesNormallyC` proves
   every schedule reaches main's `.normal`, and for THIS program a
   `.normal` completion requires the real rendezvous (main's receive
   can only complete through the worker's send — pairing or wake are
   the machine's only routes past the park). The communication
   evidence lives in the boring executable half, per the
   TCB-grounding principle (§3).
4. The D1-BOTH pair: `chanRendezvousReadoutC` (run-conditioned
   first-order readout: every `.normal` completion leaves the harness
   and handle cells intact — every `InitialSplit` premise discharged
   at the concrete seed) + `chanRendezvousTerminatesNormallyC` (the
   seeded completion pin via `allStreamsOkPool` kernel certificate,
   `#eval`-confirmed before `decide +kernel`, then
   `execProgLoop_mono`). Interpreter vocabulary only; deletion test:
   Iris appears in no statement.

**What the exemplar's triple does NOT say, stated in its docstring**:
nothing about the value 42 (protocol layer, slice 2 — the fork/join
GOLDEN certificates carry the 42 verdict at seeded ∀-schedule
strength beside it); nothing about deadlock-freedom at ∀-heap
strength (P-S4-1's `ProgressExecC`, the pool-reachability lane).

**The sequential-degenerate probe witness (`chanOpsProbe`)**
[SUPERSEDED as designed — what shipped is the close-only
`Specs/ChanCloseProbe.lean`; make/len-cap and this fuller probe are
P-CL1-6] for the
owned-cell laws + make/close (+ len/cap if shipped): a single-thread
program — make a buffered channel (cap 1), send 1 (enqueue branch),
close, receive (drain branch), receive (closed-zero branch) — walked
with the owned-cell forms. Its buffered-send step carries the phantom
pairing branch (§1a), so its walk's post is stated disjunctively or at
the join point where the branches reconverge; the witness docstring
says exactly which branches it exercises. (Whether both the phantom
and enqueue branches reconverge cheaply is a build-time question; if
not, the probe splits into per-law micro-witnesses — the honest
fallback, recorded in the build log.)

## 5. Perennial comparison (shape reference, deltas both directions)

Reference: `deps/perennial/new/golang/theory/chan.v` (read at the
pinned checkout; their new channel library).

- **Their shape**: persistent `is_chan ch γ V` + exclusive logical
  state `own_chan γ (chanstate)`; per-op lemmas (`wp_send`,
  `wp_receive`, `wp_close`, `wp_make1/2`, `wp_cap`) in HoCAP
  atomic-update style (`send_au`/`recv_au`/`close_au` — the client
  presents an accessor to the logical state at commit time), with
  later-credits in the premises. Select via `wp_try_comm_clause_*`
  over an arbitrary clause list.
- **Ours (this slice)**: laws over the PHYSICAL cell under an
  invariant accessor (`S`-shaped), no logical channel state yet; the
  au-style layer is the slice-2 protocol layer's derivation target
  over `own_chan`'s analogue (GhostMap/Auth at the pin, FD9).
- **Deltas, ours-weaker**: no value protocol (delivered values
  ∃-absorbed, §1a); no select laws yet; parked-sender law scoped to
  empty-buffer/cap-0; per-op laws are CEK-position laws (apply
  positions), not function-call specs — a client applies them inside
  a walk rather than composing sealed triples.
- **Deltas, ours-different-not-weaker** (no strictly-stronger claims
  without proof): our park/release decomposition is a class their
  spin-loop blocking model does not have (their WP never exhibits a
  parked thread — blocking is a loop that stays reducible); our laws
  feed an exit whose output (`GoTripleC`) is an interpreter-level
  first-order judgment over the differentially tested `execProg`,
  with the D1-BOTH completion pin — the standing instrument delta
  (§7.2 of the comparison doc), not re-argued here.
- Their laws burn explicit later credits (`£1 ∗ £1 ∗ £1 ∗ £1`); ours
  take the `|={E}[E]▷=>`-shaped continuations of the house kit — a
  bookkeeping difference at this layer.

## 6. Proof plan (build order) and gate plan

1. Design note (this file) — commit 1.
2. `proofs/GoLeanProofs/ChanD.lean`: the inversion kit
   (chan-op arrival/`applyPairing` state lemmas: send-pair is pure
   control at empty buf; recv-pair delivery shapes; close/no-pair;
   waiter-index ≠ arriver) + the §3a cores + the §3 rendezvous four
   (+ close/make/len-cap as budget allows) — each law lands in the
   same commit as the witness that consumes it (2–4 commits by
   concern: cores+loads, send/recv+park laws+exemplar walk,
   owned-cell probe).
3. `proofs/GoLeanProofs/Specs/ChanRendezvous.lean`: program, seed,
   invariant, the witness walk, `chanRendezvousTripleC`, the D1 pair,
   kernel cert (fuel measured; `#eval` first).
4. Audit registrations (name-tripwire scope block per house form) +
   root import + `scripts/ci` green at every commit; the 48
   designated statements byte-identical (nothing here touches
   Challenge/Solution/judge-config); zero corpus drift (no
   `GoLean/GoCore` edits planned at all — if an inversion helper
   turns out to need a GoCore-side lemma it goes in `proofs/` over
   the public API, or is recorded).

## 7. Parking ledger (slice-1, reversible courses taken)

- **P-CL1-1 — buffered parked-sender law** (§3). RE-DIAGNOSED at the
  S1 audit fix round: the entry first named the storeLoc round-trip
  lemma as the blocker (release construction at nonempty buffers) —
  overcorrected in turn (round 2): the RELEASE construction never
  needed the round-trip — constructible for free from an empty-buffer
  cell elsewhere (`crossChannelSendRelease`, the phantom-completion
  envelope member) — but BOTH of these obstacles are real: (i) the
  phantom completion skips the enqueue, so a buffered parked-sender
  law cannot state "the value ends up in the buffer" on this Language
  — that statement needs the protocol layer's ghost tie or the O1(b)
  refinement (P-CL1-4); AND (ii) the WAKE branch is live for a
  buffered parked sender (once the buffer drains, `resumeThread`
  enqueues through `storeLoc`), so the law's wake case genuinely
  needs the cell-update machinery the original entry pointed at.
  Course unchanged: law scoped to empty-buffer parks (covers cap-0).
  Consumer: buffered-park rows (slice 3), jointly with slice-2
  design.
- **P-CL1-2 — select law family** (§3): designed here, deferred on
  budget; consumer: the select-tricky trio's frame-quantified rows
  (slice 3). Course: trio remains on its certificate family.
- **P-CL1-3 — au-style (HoCAP) restatement** (§2): lands WITH the
  slice-2 protocol ghost as a derivation over this slice's laws.
- **P-CL1-4 — O1(b) phantom-pairing refinement** (§1a): a slice-2
  design question; course: absorb the branches.
- **P-CL1-5 — targeted-receive delivery walk at ∃-values** (§4): the
  general store-of-∃-value lane (typed target stores of adversarial
  values); course: zero-target exemplar; consumer: protocol-layer
  rows whose invariant pins the value class first.
- **P-CL1-7 — general-`S` law forms: SCOPE REDUCTION recorded as a
  ledger item** (S1 audit fix round; previously only a build-log
  bullet). The shipped invariant-form laws are RENDEZVOUS-CLASS
  (cell pinned to `chanData #[] 0 false`), not the §3-designed
  `S`-parameterized forms — reason: unwitnessed `S`-branches are the
  scaffold smell. Course: §3 stays the growth path; consumers: the
  buffered/close-sharing rows (slice 3) and the protocol layer's
  au-restatement (P-CL1-3).
- **P-CL1-6 — make / len-cap laws: designed (§3), NOT shipped this
  slice** (budget: each needs its own core-port and witness walk, and
  a buffered probe's post must absorb the phantom-pairing branch
  reconvergence, §4). CLOSE left this entry — shipped as
  `wpD_close_owned` with the close-probe witness (build log, commit
  3): the owned-cell form covers the write path without the phantom
  problem, since a close apply has NO pairing branch
  (`chanArrivalPlan_close`). The §3 designs for make/len-cap stand as
  the intended statements; consumers: the buffered probe and the
  slice-3 rows. Deviation from work-plan item 3 logged here honestly
  rather than half-shipped.

## 8. Build log (appended as built)

- **Commit 2 — the rendezvous law family + THE EXEMPLAR, same-commit**
  (`proofs/GoLeanProofs/ChanD.lean`,
  `proofs/GoLeanProofs/Specs/ChanRendezvous.lean`; Audit block added,
  root import wired). Decisions made DURING the build, recorded:
  - **Law scoping: RENDEZVOUS-CLASS, not general-`S`** (amends §3's
    presentation, not its design). The shipped laws
    (`wpD_send_rendezvous_inv`, `wpD_recv_nil_rendezvous_inv`,
    `wpD_blocked_send_rendezvous_inv`,
    `wpD_blocked_recv_nil_rendezvous_inv`) pin the invariant cell to
    `chanData #[] 0 false` (any `declaredTy`) instead of carrying the
    `S`-parameterized branch obligations: every `S`-branch beyond the
    rendezvous class (closed-panic, buffered enqueue/dequeue,
    head-refill) would ship without a witness discharging it —
    exactly the unconsumed generality the non-vacuity gate exists
    for. §3 remains the recorded growth path; the general-`S` forms
    land with the buffered/close consumers (slice 3 rows). The
    branch-continuation FORM settled during the build: one
    continuation over a pure successor disjunction
    (`∀ c', ⌜c' = park ∨ c' = next⌝ -∗ WP c'`), so the caller keeps
    every resource in both branches (a `∗`-pair of continuations
    would force splitting the frame; BI `∧` costs proofmode
    ergonomics).
  - **FINDING — the parked SELF-STEP (`pairRelease` re-admits the O2
    spin).** `StepDC.pairRelease` constrains `ts'[j]? = some p'` with
    the pairing's arriving/partner indices ∃-quantified — when the
    ∃-pairing's partner is some OTHER index, `ts'[j] = p` and the
    rule admits `p → p` (state-preserving) for ANY parked `p`
    whenever the current state can host any state-preserving pairing
    at all (an empty-buffer cell suffices —
    `stepDC_parked_spin`). The decomposition note's O2 record says
    "NO spin rules — O2(b) sufficed"; that is true of the RULE SET
    but the spin exists as a derived member of `pairRelease`'s
    envelope, invisible until a WP had to walk a parked config (the
    spawn-noop witness never did). Consequences, both directions:
    (i) parked-config WPs need Löb induction (the parked laws prove
    it internally — one `iloeb`, the self-branch re-applies the IH);
    (ii) parked-config REDUCIBILITY is free at empty-buffer cells
    (the spin is the NotStuck witness), which is what lets the
    parked laws avoid the wake-readiness case analysis the S4 note
    expected. Sound-wider, per the standing envelope argument — the
    simulation direction is untouched. Recorded here as the slice's
    main design finding; the O1(b) refinement (P-CL1-4) would remove
    it along with the phantom pairings.
    CORRECTED at the S1 audit fix round (the downgraded-major's
    confirmed core): the finding as first recorded UNDER-stated the
    derived envelope — beside the self-step, the non-self release
    branch can be a **phantom COMPLETION**: `applyPairing` never
    reads the PARTNER's channel (its partner patterns wildcard it),
    and `pairRelease` ∃-quantifies the whole imagined pool and its
    pre-state, so a parked sender releases to `.next k` off a pairing
    on a DIFFERENT channel — no partner, no handoff, no delivery, no
    cell write (`crossChannelSendRelease`,
    `Specs/ChanVacuityWarning.lean`, axiom-clean). The original
    "genuine release — the partner completed the handoff; the
    ∃-pairing carried the delivery" reading was FALSE as a
    per-branch characterization: a release to `.next k` carries NO
    delivery information whatsoever. The shipped laws remain sound
    (their successor enumeration `{p, .next k}` is proved over ALL
    arms — `applyPairing_partner_write`); the corrections land in
    the law docstrings, in P-CL1-1's re-diagnosis below, and in the
    slice-2 consequence: the protocol layer can NEVER infer "parked
    sender reached `.next k` ⇒ its value was delivered" from the
    Language — value transfer must be tied by ghost state, not by
    control flow.
  - **`wpD_fork_alloc₁` shipped** — the gen_heap-update fork variant
    LangC recorded as "lands with its first consumer": the exemplar's
    one-parameter worker is that consumer (`bindParams` allocates the
    param cell; the child's WP receives it ∀-address).
  - **The untyped-literal wrinkle:** `.intLit 42` evaluates at kind
    `unbounded "integer"` (Go untyped constant), so the send-law
    witness normalizes `int 42 unbounded → int 42 int` via
    `rdvNorm42` (σ-independent, `[propext]`); the fork's `bindParams`
    normalization rides `rdvNormChan`. Both are exemplar-local
    helpers, not laws.
  - **Figures** (measured): exemplar cert
    `chanRendezvousAllStreamsCert` at fuel 400, `#eval`-confirmed
    `true` before `decide +kernel` (with a plain-run probe and the
    seed's `MachineWf` decide, all three eval'd first); axiom sets —
    inversion kit `[propext]`/`[propext, Quot.sound]` (constructive),
    Iris-side laws + exit artifacts the classical trio, cert
    `[propext, Quot.sound]` — FD7 exactly. The walk elaborates under
    `maxHeartbeats 3200000` (the noop witness needed 1600000; this
    walk is roughly twice the steps plus two invariant openings per
    channel position).
  - Witness structure: `chanRendezvousTripleC` (the exit's product) +
    the D1-BOTH pair `chanRendezvousReadoutC` (InitialSplit
    discharged at the seed via `sat_sep_insert`; three-cell heaplet)
    and `chanRendezvousTerminatesNormallyC` (seeded completion pin,
    `execProgLoop_mono` lift). Nothing designated (FD3); the 48
    designated statements untouched (git diff over the branch range:
    Challenge/Solution/judge-config and every designated module
    untouched).
  - **Gate** (CORRECTED at the S1 audit fix round, finding C1 — the
    first form of this bullet said "at this commit's tree", which the
    artifact's own metadata contradicts): full `scripts/ci --diff`
    run IN-LANE (this worktree's first recorded differential — the
    documented fresh-checkout red; `GOLEAN_MEM_MAX=48G` per the
    parallel-lane cap discipline): **PASS, baseline diff FULL
    (1483/1483, no regression), negative lane no regression**, proofs
    + Audit green with the new registrations. The record's meta:
    `git_commit c1a619b8` (commit 1) with `git_dirty true` — the run
    executed over the commit-2 content while it was still IN-TREE,
    before commit 2 existed, so later `scripts/ci` invocations mark
    it stale. Mitigation (verified at the audit): the whole branch
    diff touches only `docs/` + `proofs/`, so the differential
    surface is unchanged and the result transfers; and the fix
    round's clean-tree re-run at its tip (§9) supersedes this record.
    ci now surfaces dirty-meta records on every judgment line (the
    §9 hardening).

- **Commit 3 — the CLOSE law (the family's write-path member) +
  probe witness.** `wpD_close_owned` (`ChanD.lean`): close on an
  OWNED open cell — the one channel law that WRITES the cell through
  the D-carrier (`closed := true`, buffer/capacity preserved; the
  cell in the machine-real untyped shape `makeChan` allocates). The
  key structural fact: a close apply has NO pairing branch —
  `chanArrivalPlan` has no `.close` arm (`chanArrivalPlan_close`,
  proved `rfl`) — so unlike send/recv the successor is deterministic
  and no invariant is needed when the closing thread owns the cell
  (the sequential-degenerate class; the invariant sibling is recorded
  with a sharing consumer, P-CL1-6's neighbor). WITNESS
  (`Specs/ChanCloseProbe.lean`): the close-probe walk —
  `chanCloseTripleC` is the first frame-quantified triple whose POST
  records a channel-cell state change — with the D1-BOTH pair
  (`chanCloseReadoutC`, `chanCloseTerminatesNormallyC`; cert fuel 20,
  `#eval`-confirmed true before `decide +kernel`, MachineWf decide
  eval'd too). Axioms: FD7-exact (law/witness classical trio;
  inversion + cert constructive). Audit block extended; root import
  wired; `scripts/ci` green (the slice's recorded differential
  stands — zero runtime edits in this commit either).

## 9. S1 audit fix round (2026-08-11; 1 confirmed major, 1 downgraded
## minor with confirmed core, 2 confirmed minors, notes)

[§§9-15 below are kept in full as THE RECORDED LESSON of the gate
arms race — six adversarial review generations against successive
completion-gate mechanisms, each finding an escape. The user ruling
that ended it, and the cleanup that followed, are §16. Nothing below
describes current machinery except where §16 says so.]

- **Fix A — THE MAJOR (the nil-park/vacuity story).** §3's nil-channel
  paragraph rewritten to the truth (see it for the full account); the
  protection story restated per the TCB-grounding principle (user
  doctrine 2026-08-11): trusted = boring interpreter propositions
  (completion pin + readout), machinery = untrusted method. Enforced:
  the COMPLETION-PIN GATE (`Audit.lean` — every
  `GoLeanProofs.Specs.Chan*` module declaring a `GoTripleC` theorem
  must declare a `TerminatesNormallyC` companion; fail-closed anchor/
  scope guards; negative-tested against the fixture). The verifier's
  deadlock-triple probe is now the PERMANENT warning fixture
  `Specs/ChanVacuityWarning.lean` (negative knowledge, kept forever):
  `deadlockRecvTripleC` through the shipped laws beside
  `deadlockRecvDeadlocks` (the kernel-evaluated deadlock), plus the
  three pinned envelope members (`nilParkSpins`, `nilParkReleases`,
  `crossChannelSendRelease`) the corrected §3/§1a cite.
- **Fix B — the phantom-completion correction** (the downgraded
  major's confirmed core): the §8 SELF-step finding, both parked-law
  docstrings, and P-CL1-1 corrected — a release to `.next k` carries
  NO delivery information (the imagined pairing can sit on a
  different channel entirely); the slice-2 consequence (ghost-tied
  value transfer, never control-flow-inferred) recorded at each site.
- **Fix C — the TCB-grounding retrofit** (§10, the walk over every
  exported artifact) + the charter addendum making the walk a
  per-slice review criterion for the rest of the arc.
- **Fix D — the confluent-lane discharge** (§11): the charter's own
  validation addition, owed by finding C2 — per-law corpus mapping
  recorded and the seven-case slice RUN first-hand (7/7 PASS, the
  fork-join/rendezvous rows confluent-certified `|set|=1`).
- **Fix E — exemplar framing scoped** (downgraded-to-note, applied
  anyway): the "genuine cross-goroutine" sentence in the module
  docstring, the route §4 item 3, and the Audit block now state that
  the triple alone is compatible with a never-communicating program
  and that the completion pin carries the communication evidence.
- **Fix F — records batch**: the `wpD_fork_alloc₁` fork-debt claim
  scoped to the D-carrier with LangC's `wpC_fork` record
  back-annotated (the C-carrier variant remains unbuilt); the S4
  decomposition note's "NO spin rules" back-annotated in place; §4's
  stale makeChan/`chanOpsProbe` forward references annotated (they
  point to P-CL1-6); the general-`S` scope reduction promoted to a
  ledger entry (P-CL1-7); the Audit blocks' "every public theorem of
  both modules" sentences rescoped to the four-module reality; the
  commit-2 gate bullet corrected to the artifact's own metadata
  (finding C1) and `scripts/ci` HARDENED — dirty-meta records now
  print a visible warning marker on every baseline-diff judgment
  line (choice: WARN, not fail — the tight loop legitimately records
  dirty mid-iteration runs; handoff-quality claims must cite a
  clean-tree record; reason recorded at the ci site too).
- **Fix G — the clean differential record** (finding C1's re-run
  half): full `GOLEAN_MEM_MAX=48G scripts/ci --diff` at the fix
  round's tip 403e2356, COMMITTED CLEAN TREE — the artifact's own
  meta now reads `git_commit 403e2356`, `git_dirty false`,
  `manifest_cases 1483`. **RESULT: PASS — baseline diff FULL
  (1483/1483, no regression), negative lane 311 no regression, all
  gates green** (incl. the new completion-pin gate and the dirty-meta
  marker path, which this clean record does not trip). This entry
  lands as a DOC-ONLY commit directly on top of 403e2356 (the
  established S4-precedent discipline: the run's meta names its
  commit; the recording commit changes no differential surface — the
  branch's only non-doc, non-proofs file remains scripts/ci itself,
  whose change is the reporting marker above).

## 10. The TCB-grounding walk (retrofit, S1 audit fix round — the
## per-slice review criterion from here on)

Doctrine (user, 2026-08-11): for every soundness property, the TRUSTED
claim must be a boring, semantically-trivial property of the
interpreter; Iris/Löb/simulation are untrusted METHOD only. The walk
below names, for every exported artifact of this slice: (i) the boring
trusted endpoint — the interpreter proposition the statement reduces
to; (ii) that all machinery is proof-side (the deletion test:
`Audit.lean`'s statement-TCB gate mechanizes it for designated
statements; none of these are designated, but each statement below is
Iris-free and relation-free by the same reading); (iii) the executable
anchor.

| exported artifact | (i) trusted endpoint (interpreter vocabulary) | (iii) executable anchor |
|---|---|---|
| `chanRendezvousTripleC` | ∀ admissible seeded heap, ∀ fuel/stream: `execProg … = .ok (.normal σf, _)` → the harness+handle bindings survive in `σf.heap` | run-conditioned only — anchored by the pin row below; the warning fixture documents why the triple alone anchors nothing |
| `chanRendezvousReadoutC` | the same, first-order at the concrete seed (`loadLoc σf … = .ok …`) | premises discharged at the seed; consumes the triple as method |
| `chanRendezvousTerminatesNormallyC` | ∃N ∀fuel≥N ∀ch: `execProg … = .ok (.normal …, _)` | `chanRendezvousAllStreamsCert` — kernel evaluation of `allStreamsOkPool` (fuel 400), `#eval`-confirmed first; `execProgLoop_mono` lift |
| `chanCloseTripleC` | ∀ admissible heap, run-conditioned: handle intact ∧ data cell `chanData #[] 1 true` in `σf.heap` | pin row below |
| `chanCloseReadoutC` | first-order at the seed | consumes the triple |
| `chanCloseTerminatesNormallyC` | ∃N ∀fuel≥N ∀ch completion | `chanCloseAllStreamsCert` (fuel 20, `#eval`-first) |
| `deadlockRecvDeadlocks` (+`…Adv`, warning fixture) | `execProg 200 … = .error .deadlock` under the canonical / a pinned adversarial stream (∀-stream deliberately unproved — `transferable` excludes `.deadlock`; scope at the theorem) | itself — kernel evaluation; THE fixture's trusted content |
| `deadlockRecvTripleC` (warning fixture) | (vacuous by design — no completing run is exhibited, and the pinned-stream runs deadlock; the ∀-stream no-completion claim is deliberately unproved, like the deadlock's — scope at `deadlockRecvDeadlocks`) | none, deliberately: the fixture demonstrates exactly this |

Everything else this slice shipped — the `wpD_*` laws, the lifting
cores, the inversion kit, the WP walks, `StepDC` facts — is METHOD:
none of it appears in any exported statement (the statements above
mention only `execProg`/`loadLoc`/`GoTripleC`/`TerminatesNormallyC`,
all interpreter-vocabulary surface definitions), and the differential
(§11) plus the kernel certificates are what ground the interpreter
itself. The D1-BOTH convention (triple + completion pin ship together) is
held BY REVIEW — the audit dimension checks it per slice — not by a
build gate (user ruling 2026-08-11, §16: gates are speedbumps
against honest mistakes; adversarial-grade gate certainty is neither
reachable nor needed). One dumb speedbump remains in `Audit.lean` (a
`Chan*` Specs module with a `*TripleC`-named theorem should have a
`*TerminatesNormallyC`-named one; trivially evadable by design, with
the threat-model comment saying so). Pre-side vacuity stays exactly
where this table puts it — in the witness discipline (each readout
row discharges its `InitialSplit` at the pin's own seed).
The matching charter addendum makes this walk a per-slice review
criterion for the rest of the arc.

## 11. The confluent-lane discharge (charter validation addition,
## owed by the audit's C2 — recorded and RUN at the fix round)

The charter's addition: every new law's soundness is also exercised
through the CONFLUENT lane where a deterministic concurrent program
exists for its shape. Discharge, per law — the laws are proof-layer
over the SAME `applyChanOp`/`arrivalPlan`/`applyPairing`/
`resumeThread` code paths the differential executes, so the corpus
cases below exercise each law's machine positions end-to-end against
`go run`:

- **send/recv apply + parked send/recv (rendezvous four)**:
  `goroutines/fork-join/unbuffered` (the exemplar's exact shape —
  spawn, unbuffered send, receive) and
  `goroutines/rendezvous-hb/send-hb` (confluent; carries the
  zero-target receive `<-done`, the exemplar's discard idiom) — both
  CONFLUENT-lane rows: the enumerator certifies |set|=1 over ALL
  schedules, then strict go-run equality (full-strength differential
  for deterministic concurrent programs — the charter's requested
  lane). [CORRECTED at audit round 2: this bullet first cited
  `goroutines/fork-join/result-discarded` as the zero-target-receive
  row — false, its receive is targeted (it discards the goroutine's
  RETURN value); the id is dropped from the discharge and the
  zero-target shape is carried by `rendezvous-hb/send-hb`.]
- **`wpD_fork_alloc₁` (the allocating fork)** [ADDED at audit round
  2 — the first form of this section omitted the law entirely]:
  `goroutines/fork-join/args-eval-now` (CONFLUENT-lane, `go
  func(v int){…}(…)` — a one-parameter spawned callee, exactly the
  `bindParams`-allocating spawn class the law covers).
- **close (owned)**: `channels/close-closed-panic`,
  `channels/closed-receive`, `channels/close-edge/drain-zero-after-close`
  (strict lane — the close probe's single-goroutine class is
  sequential-degenerate, where strict IS the full-strength check).
- **make/len-cap (P-CL1-6, laws unshipped)**:
  `builtins/make-channel-len-cap` stands ready as their case.

RUN first-hand (re-run at audit round 2 with the corrected id set —
`fork-join/unbuffered`, `fork-join/args-eval-now`,
`rendezvous-hb/send-hb`, the three close rows,
`make-channel-len-cap`): **7/7 PASS**, the three goroutine rows at
`stage=confluent` with `|set|=1 certified over all schedules`
(observations recorded in the run detail). The exemplar programs
themselves are Lean-side seeds (hand-built `Stmt`, no frontend
lowering), so they are exercised by the kernel certificates
(`allStreamsOkPool` — schedule-exhaustive at the seed) rather than by
new corpus rows; the corpus rows above pin the same shapes through
the full frontend+oracle pipeline. No new corpus case was added
(zero corpus effect stands); if a future slice lowers the exemplars
through the frontend, they become ordinary confluent rows.

## 12. S1 audit round 2 (delta review: 1 confirmed major + 8 confirmed
## minors — the gate's name/glob/module mechanics were escapable)

- **THE GATE, REBUILT SEMANTIC** (the major + the convergent minors,
  on the statement-TCB gate's own idiom): classification = the TYPE's
  transitive `defnInfo`-unfolding closure reaching `GoTripleC` (kills
  the `GoSpecC` blindness, the wrapper escape, and any future
  wrapper); scope = ALL `GoLeanProofs.Specs.*` (the `Chan*` glob is
  gone); kinds = `theorem` AND `def` (recorded choice for (d):
  classify, don't refuse); pairing = per-PROGRAM (the triple's
  extracted `prog` argument must have a `TerminatesNormallyC` pin for
  the SAME program anywhere in scope — implemented, the preferred
  branch of (c); cross-module pins legitimate, the golden row's pin
  lives in `TotalPins`); wrapper-hidden triples (classified but no
  extractable saturated application in the stated type) FAIL CLOSED;
  the PIN side stays a shallow syntactic scan (recorded per the
  verifier's asymmetry note — its failure direction is a loud
  spurious failure, never a silent pass); budget exhaustion on the
  walk throws. Gate output at this round's tip: 17 triple-carrying
  constants, 22 pin instances, all non-fixture exports
  program-paired.
- **Eleven completion pins** so every pre-existing `GoSpecC` export
  carries its genuine POOL-carrier ∃-completion member (preferred
  over grandfathering, per the round's direction): the kit lemma
  `goSpec_seeded_terminatesNormallyC` + the carrier transfer
  `terminatesNormallyC_of_terminatesNormally` (Surface — sequential
  completion lifted by conservation; `transferable (.ok _)` is the
  hinge), instantiated per row — NilWP ×5, NewWP ×2, VarsWP ×2,
  BlockWP ×1, and `goldenTerminatesNormallyC` (TotalPins) for
  `goldenSpecC`. No designated STATEMENT changed — the pins are new
  theorems beside them (statement-TCB gate green, 48 unchanged).
- **Escape-shape fixtures** (`Specs/ZzVacuityGateFixtures.lean`,
  tracked): `fixtureSpecCUnpinned` (GoSpecC-typed), `fixtureDefTriple`
  (def-exported), `fixtureWrappedTriple` (wrapper-hidden → the
  fail-closed arm), in a module whose own name is the out-of-glob
  scope fixture; all honest vacuous-by-unsatisfiable-pre proofs
  (recorded deviation: the review's `.tmp` GoSpecC probe used `sorry`,
  which the axiom sweep forbids — the tracked fixtures demonstrate
  the same escape SHAPES honestly, and double as permanent reminders
  that unsatisfiable-pre triples are vacuously true). The gate's
  negative tests assert each fixture flags in its expected class.
- **"Deadlocks on every schedule" scoped to the proved claim** at all
  three sites (fixture header, §3, Audit anchor) + an
  adversarial-stream sibling pin added (`deadlockRecvDeadlocksAdv`).
  Choice recorded: prose-scoping over ∀-stream strengthening — the
  strengthening is NOT mechanical, because the conservation kit's
  `transferable` class deliberately excludes `.deadlock` (no lemma
  transfers or quantifies deadlocking runs over streams); recorded at
  the theorem as the honest gap.
- **P-CL1-1 restated with BOTH obstacles** (below, in place): the
  round-1 re-diagnosis overcorrected — the phantom completion blocks
  the "value ends up in the buffer" statement, AND the wake branch
  still enqueues through `storeLoc` (a buffered parked sender's wake
  is live once the buffer drains), so the storeLoc/store-update
  machinery is genuinely needed by the wake case even though the
  release construction never needed the round-trip.
- **§11 corrected + re-run**: `fork-join/result-discarded` dropped
  (its receive is targeted — it discards the goroutine's RETURN
  value, not the received value); the zero-target shape is carried by
  `rendezvous-hb/send-hb`; `wpD_fork_alloc₁` gained its missing
  discharge row (`fork-join/args-eval-now`, the one-parameter
  allocating-spawn confluent case); the corrected seven-id slice
  re-run first-hand, 7/7 PASS.
- **ci hardening completed fail-closed**: a meta lacking `git_dirty`
  is now treated as dirty/unknown (marked, not silently clean); the
  negative lane's judgment line states its no-metadata attribution
  gap honestly (it publishes no meta at all — recorded); the round-1
  "every baseline-diff judgment line" claim corrected accordingly.
- **Commit-2 gate bullet range-scoped** (its "whole branch diff"
  mitigation was made false by the fix rounds touching `scripts/ci`):
  now stated over the record's own range `d5696de1..c7251faa`.
- **§3 scoped and unlinked**: the nil-park-law provability claim is
  scoped to the tracked step-level witnesses (a law is derivable but
  deliberately unshipped — no consumer); the false "Consequently"
  linkage removed (the deadlock demonstration needs no nil channel).
- **The round-2 clean differential record**: full
  `GOLEAN_MEM_MAX=48G scripts/ci --diff` at the round-2 tip
  `1c7e6e06`, committed clean tree — meta `git_commit 1c7e6e06`,
  `git_dirty false`, `manifest_cases 1483`. **RESULT: PASS — baseline
  diff FULL (1483/1483, no regression), negative lane 311 no
  regression** (its judgment line now carrying the recorded
  no-metadata note), all gates green including the REBUILT semantic
  completion-pin gate (17 classified / 22 pins / fixtures flagged)
  and the statement-TCB gate at 48 designated, byte-identical. This
  entry is the round's doc-only record commit over the run's own
  commit, per the established discipline.

## 13. S1 gate-verification round (round 3: 1 critical + 2 major +
## 2 minor + 1 note — all in the rebuilt gate; NOT_CONVERGED → fixed)

- [CORRECTED at gen 5: this round's record claimed "the gate section
  was swept for remaining `| _ =>` arms — none remain" — FALSE; three
  remained, all fail-closed (the two `Expr`-leaf arms in
  `gateCollectApps` and the pin pass's non-`.const` head, each
  strict-direction). The false sweep claim is exactly the
  self-report class the gate-honesty dimension checks; recorded.]
- **CRITICAL — the walk's `| _ => pure ()` wildcard was fail-open**
  (structure/inductive wrappers with out-of-scope pieces escaped,
  invisible even in the counts) — a VERBATIM regression of the
  2026-08-01 defect recorded at the statement-TCB gate's own
  docstring; **the repo has now grown this bug twice**, and the gate's
  comment says so. Fixed per the verifier's validated patch: the
  dependency-edge rule matches every `ConstantInfo` case explicitly
  (`.opaqueInfo → value`, `.inductInfo → ctors`, thm/axiom/ctor/rec/
  quot type-only), NO wildcard — a new kind is a compile error. The
  reachability computation was also restructured to ONE reverse-BFS
  from `GoTripleC` over GoLean-module constants (Iris/Std constants
  cannot reference it), replacing per-root walks.
- **MAJOR — open-term pairing**: the two generic pin lemmas
  contributed bare de Bruijn indices (`#1`, `#4`) to the pin set, so
  a triple's bound-variable prog could "pair" by binder-depth
  collision. Fixed: open pin programs are dropped; a classified
  export with an open extracted prog is the OPEN-TERM fail-closed
  class (fixture `fixtureOpenProgTriple`); genuine ∀-program lemmas
  (`goSpecC_of_goSpec`, `goTripleC_of_wpD`) live on an EXACT-NAME
  allowlist with per-name reasons at the gate.
- **MAJOR — mention-is-not-assertion**: round 2 counted ANY
  `TerminatesNormallyC` application anywhere in a type as a pin —
  self-pinning hypotheses and non-assertive decoys included. Fixed: a
  pin is a theorem/def whose CONCLUSION (after the binder telescope)
  has `TerminatesNormallyC` as its head over a CLOSED program;
  fixtures `fixtureSelfPin` + `fixtureDecoyPin`/`fixtureDecoyTriple`
  pin the two escape shapes.
- **MINOR — prefix exclusion**: fixture exclusion is now exact-name
  plus a generated-suffix whitelist (`eq_*`, `match_*`,
  leading-underscore, numeric); a user-declared namespace child is
  flagged and must be listed exactly (fixture
  `fixtureDefTriple.namespaceChildProbe`). The P2 structure's three
  compiler-generated satellites (projection/casesOn/recOn) are
  exact-listed with the reason at the gate.
- **MINOR — scope**: enforcement is ENV-WIDE over the proofs package
  (`GoLeanProofs` + `GoLeanProofs.*`) — `spawnNoopTripleC` (LangD) is
  now enforced and pairs with its existing pin; a module named
  exactly `GoLeanProofs.Specs` is covered; fixture
  `fixtureOutOfSpecsTriple` (in the non-Specs
  `ZzGateFixtureSupport`) proves the widening structurally. No
  allowlisted namespace carve-outs — the only allowlist is the
  two-name generic-lemma list.
- **NOTE — prose residues**: the fixture program abbrev's docstring
  and the §10 table row no longer claim "every schedule"/unscoped
  no-completion; both point at `deadlockRecvDeadlocks`' recorded
  scope.
- **COUNTS, explained** (the record the round demands): round-2's
  "17 classified / 22 pins" → round-3's **27 classified / 21
  conclusion-asserted closed pins / 2 allowlisted**. Classified: +9
  new tracked fixtures +3 fixture-structure satellites +spawnNoop
  (env-wide) −2 generics (moved to the allowlist, no longer counted).
  Pins: −2 open-term bvar "pins" (the round-2 escape, gone by
  design) +1 `spawnNoopTerminatesNormallyC` (env-wide scope now sees
  it). Fixtures flagged: 7 unpaired + 2 wrapper-hidden + 1 open-term,
  every one negative-asserted in its class.
- **The round-3 clean differential record**: full
  `GOLEAN_MEM_MAX=48G scripts/ci --diff` at the round-3 tip
  `d1cf54b8`, committed clean tree — meta `git_commit d1cf54b8`,
  `git_dirty false`, `manifest_cases 1483`. **RESULT: PASS — baseline
  diff FULL (1483/1483, no regression), negative lane 311 no
  regression, all gates green** including the round-3 completion-pin
  gate (27 classified / 21 conclusion-asserted closed pins / 2
  allowlisted / fixtures 7+2+1 flagged, every negative test in-build)
  and the statement-TCB gate at 48 designated, byte-identical; audit
  sweep 13537 declarations axiom-clean. Doc-only record commit over
  the run's own commit, per the established discipline.

## 14. S1 gate-verification generation 4 (round 4: 2 latent majors +
## 3 minors + 2 notes — the LAST patch round by operator direction)

- **MAJOR — the kind-filter wildcard** (the round-3 critical's exact
  signature one level up: `kindOk`'s `| _ => false` silently dropped
  `opaque` exports, count-invisible). Fixed: `exportKind` matches all
  eight `ConstantInfo` cases explicitly with per-arm reasons (a new
  kind is a compile error); the gate section was swept for remaining
  `| _ =>` arms — none remain. Fixtures: `fixtureOpaqueTriple`
  (opaque export, UNPAIRED) and `fixtureOpaqueEdge` (the
  `.opaqueInfo → value` EDGE arm's mutation trigger, WRAPPER-HIDDEN —
  round 3 had NO fixture on that arm and its negative-test message
  misleadingly claimed otherwise; message fixed).
- **MAJOR — hypothesis-guarded pins** (`gateConclusion` peeled premise
  binders, so `(h : False) → TerminatesNormallyC …` counted). Fixed:
  a pin's TYPE must be BINDER-FREE (verified free today — all 21
  pins have zero binders). The doctrine tension is recorded at the
  pin pass: CLAUDE.md blesses genuinely-external premises on LAWS,
  but a completion PIN is the existence witness itself — a
  conditional pin, if ever legitimate, goes on an exact-name
  allowlist with the premise argued. Fixtures:
  `fixtureFalseGuardedPin` + `fixtureGuardedTriple`.
- **MINOR — suffix abuse**: exclusion under fixture roots is EXACT
  LIST ONLY (the generated-suffix whitelist was abusable); the P2
  structure's satellites are exact-listed (now four — the
  `mk._flat_ctor` def surfaced when the name skip narrowed). Fixture:
  `fixtureDefTriple.eq_realExport` — plus a direct negative test ON
  the exclusion FUNCTION (a non-listed pseudo-generated child must
  not be excluded), because that mutation changes only enforcement
  and no declared fixture can see it.
- **MINOR — `isInternal` over-skip**: the name skip is now
  `_private`-rooted only; user-writable leading-underscore names
  classify. Fixture: `_fixtureUnderscoreTriple`.
- **MINOR — pairing key**: now `(env₀, prog)`, both closed (a pin
  under one environment no longer anchors an export under another).
  Fixture: `fixtureEnvMismatchTriple` (`goldenDriver` under `[]` vs
  its pin under `outEnv`). THE RECORDED LIMIT, stated at the gate, in
  §10, and in the charter: the gate enforces anchor EXISTENCE per
  `(env₀, prog)` — it does NOT check the pin's seed against the
  export's precondition; pre-side vacuity remains the witness
  discipline's job (the D1 readout pair discharges `InitialSplit` at
  the pin's own seed). Overclaim wording removed at all three sites.
- **NOTE — reverse-edge coverage**: the `isGoLeanMod` allowlist (an
  unenforced invariant) became an upstream-root DENYLIST
  (`Init/Lean/Std/Iris/Qq/Batteries` — packages that build before
  this repo and cannot reference `GoTripleC` by lake's acyclic
  dependency order): an unknown/new module root is now INCLUDED by
  default — the failure direction is closed structurally, no
  invariant assertion needed.
- **MUTATION VERIFICATION** (all six run against the built
  environment, each firing its expected negative test): opaque-edge
  arm dropped → `fixtureOpaqueEdge not CLASSIFIED`; pin peeling
  restored → `fixtureGuardedTriple not flagged UNPAIRED`; prog-only
  key restored → `fixtureEnvMismatchTriple not flagged UNPAIRED`;
  opaque kind dropped → `fixtureOpaqueTriple not CLASSIFIED`; suffix
  exclusion restored → the exclusion-function negative test fires;
  `isInternal` restored → `_fixtureUnderscoreTriple not CLASSIFIED`.
- **COUNTS, re-explained**: round-3's 27/21/2 → round-4's **34
  classified / 21 pins / 2 allowlisted** (+6 new fixtures, +1
  `mk._flat_ctor` satellite exact-listed; pins unchanged — the
  guarded pin is REJECTED, and no new pin was added). Fixtures
  flagged: 12 unpaired + 3 wrapper-hidden + 1 open-term.
- **The restructure question** (operator asked): patching remained
  cheaper THIS round — all findings were narrow with validated
  probes, and the round-3 verifier confirmed everything else held
  under attack. IF the final verification finds another major in the
  same class, the restructure worth taking is the GENERATED-MANIFEST
  form: the gate emits the full computed classification (constant →
  class → pin key) and diffs it against a TRACKED manifest, so every
  change to the classified set becomes reviewable drift instead of a
  silent-escape surface; the checker then only needs to be trusted
  for completeness of ENUMERATION, not for per-shape rules.
- **The round-4 clean differential record**: full
  `GOLEAN_MEM_MAX=48G scripts/ci --diff` at the round-4 tip
  `074bfa54`, committed clean tree — meta `git_commit 074bfa54`,
  `git_dirty false`, `manifest_cases 1483`. **RESULT: PASS — baseline
  diff FULL (1483/1483, no regression), negative lane 311 no
  regression, all gates green** including the round-4 completion-pin
  gate (34 classified / 21 binder-free (env,prog)-keyed pins / 2
  allowlisted; fixtures 12+3+1 flagged; all six mutation triggers
  verified firing, §14) and statement-TCB at 48 designated,
  byte-identical; audit sweep 13549 declarations axiom-clean.
  Doc-only record commit over the run's own commit, per the
  established discipline.

## 15. Gen-5: THE RESTRUCTURE — the generated-manifest completion gate

Gen-5 review found the pairing key's (types, funcs, methods) axis (a
triple over an empty/different function table silently anchored by a
real pin — latent: all 14 live pairings were verified matching at gen
5) and mapped the adjacent surfaces (17 sequential GoSpec/GoTriple
exports outside the gate; the compat/gobra Surface import; the
private-decl and same-module blind spots). Per the operator's declared
terminal condition, per-shape patching STOPPED; the §14-designed
restructure landed instead:

- **The checker only enumerates** (`Audit.lean`): the reverse-BFS +
  exhaustive `ConstantInfo` walk (unbroken through gens 4-5) now emit
  a descriptor per in-scope constant — kind, class, the FULL key
  tuple (types, funcs, methods, env₀, prog) of every carrier
  application including the SEQUENTIAL carriers (`GoTriple`/`GoSpec`
  — the 17-export surface closed), and the mechanically-matched pin
  with the pin's own full (env₀, seed, prog) tuple. The trusted claim
  shrank to ENUMERATION COMPLETENESS.
- **`CompletionManifest.lean` is the record** (choice recorded there:
  a def-only Lean module, not a baselines/ TSV — no IO/cwd in the
  in-build gate, no parser to drift, same reviewability): 67 lines,
  every one dispositioned BY HAND at creation — 24 `paired-exact`
  (14 concurrent, verified matching by the gen-5 verifier + 10
  sequential, paired against the NINE new seq pins derived from the
  rows' TotalReadouts plus the pre-existing nil pin), 23
  `paired-with-stated-delta` / `allowlisted` lines with per-line
  citations (the legacy designated sequential statement-forms — incl.
  two RECORDED HONEST GAPS: `committedIndexAllConfigs`' ∀-config
  quantifier and `quorumAckedIndexFuncSpec2`'s unpinned callsite
  driver, both predating the doctrine — and the nine generic
  ∀-program lemmas), 16 fixtures + 4 satellites. Drift = build
  failure until a reviewed line lands in the same commit (the
  tracked-baseline re-pin discipline, cited at the gate).
- **The gen-5 escape class is now reviewable, not rule-anticipated**:
  a wrong-funcs export's manifest line visibly carries `f=<empty>`
  beside `pinkey=…s=rdvSeed` — verified RED: the funcs-axis probe
  drifts with exactly that line printed (this round's RED-3).
- **Verified RED** (all three coordinator scenarios): a stash-probe
  new unpinned export → `DRIFT (new/unlisted export)`; a manifest
  line flipped to `paired-exact` without the pin → `disposition
  paired-exact but computed class is unpaired`; the funcs-axis probe
  → drift with the differing tuples printed. Fixture migration: the
  16 attacker shapes are manifest lines whose computed class the
  gate re-verifies (a fixture line marked paired fails); enumeration
  mutations move computed lines and fail the diff.
- **Honesty sweep** (gen-5 minors/notes, all applied): the
  "remaining, deliberately UNCHECKED axis (singular)" wording
  replaced by the complete limits list (manifest docstring, §10,
  charter); §14's false "swept, none remain" corrected in place
  (three fail-closed `| _ =>` arms remain, named); the stale "FALLEN
  THREE TIMES" gate docstring replaced by the full five-generation
  history + restructure rationale; the private-decl skip got its
  tracked fixture (`fixturePrivateTriple` + in-gate existence/skip
  assertion) and a stated-scope line; the same-module blind spot is
  now an asserted-empty check; the denylist justification corrected
  to the actual mechanism (Lake per-library module ownership + the
  ci proofs-file closure step, not build order); the compat/gobra
  Surface-import adjacency recorded as a watched surface (zero
  triples there today, gen-5 census).
- If the follow-up focused verification finds a MAJOR in the
  restructured gate, the operator takes it to the user (recorded per
  instruction).
- **The gen-5 clean differential record**: full
  `GOLEAN_MEM_MAX=48G scripts/ci --diff` at the restructure tip
  `11d570dd`, committed clean tree — meta `git_commit 11d570dd`,
  `git_dirty false`, `manifest_cases 1483`. **RESULT: PASS — baseline
  diff FULL (1483/1483, no regression), negative lane 311 no
  regression, all gates green** including the RESTRUCTURED
  manifest completion gate (67 enumerated = 67 reviewed lines, 24
  mechanically pin-paired, 35 pins, no UNRESOLVED; three RED
  scenarios verified this round) and the statement-TCB gate at 48
  designated, byte-identical; audit sweep 13589 declarations
  axiom-clean. Doc-only record commit over the run's own commit, per
  the established discipline.

## 16. THE CLEANUP ROUND — user ruling ends the gate arms race
## (2026-08-11)

**USER RULING (recorded):** the gate arms race was an antipattern —
adversarial-grade certainty is neither reachable nor needed for a
deterrent. NEW STANDING DOCTRINE: gates are SPEEDBUMPS against honest
mistakes unless they guard the TCB; they are reviewed for
simplicity/robustness ("does it catch the honest mistake, could we
delete it"), never for adversarial escape; adversarial review stays
reserved for semantics, claims, and records. Ruthless deletion of
fragile gate cruft is the default.

**DELETED** (this round, ~940 lines):
- `CompletionManifest.lean` (343 lines — all 67 reviewed lines) and
  the manifest diff gate;
- the semantic classifier, reverse-BFS, per-shape verdict rules,
  mutation triggers, same-module and denylist assertions — the whole
  gate section's machinery in `Audit.lean` (~510 lines across its
  generations);
- all 16 gate-attack fixtures + 4 satellites
  (`ZzVacuityGateFixtures.lean`, 237 lines;
  `ZzGateFixtureSupport.lean`, 45 lines) and their Audit
  registrations. (Discovered during cleanup, recorded: the gen-5
  gate-replacement edit had already unintentionally swept the
  round-3/4 fixture registrations along with the old gate section —
  invisible because the exhaustive axiom sweep still covered the
  constants and a lost `#guard_msgs` block cannot fail a build. An
  instance of exactly the fragility the ruling names.)

**KEPT:**
- `Specs/ChanVacuityWarning.lean`'s educational core —
  `deadlockRecvTripleC` + `deadlockRecvDeadlocks`(+`Adv`) + the
  nil-park/cross-channel envelope lemmas: the permanent demonstration
  that a triple without its completion pin claims nothing. Docstrings
  trimmed of gate references; it teaches, it does not guard.
- The ELEVEN pool-carrier and TEN sequential completion pins — they
  are genuine theorems with standalone value (the D1-BOTH
  convention's ∃-completion members); their docstrings re-homed to
  the convention, not to any gate.
- ONE dumb speedbump in `Audit.lean` (~30 lines, name-based,
  module-scoped: a `Specs.Chan*` module with a `*TripleC`-named
  theorem should have a `*TerminatesNormallyC`-named one;
  `ChanVacuityWarning` excluded by name — its point is the missing
  pin) carrying the DO-NOT-HARDEN threat-model comment verbatim.
- The D1-BOTH convention as a REVIEW item (audit dimension), stated
  here and in the charter; no build gate enforces it.
- §§8-15 in full, as the recorded lesson.

**Gate figures at the cleanup tip**: audit job/declaration count
SHRANK as expected (sweep 13589 → 13531 declarations — the deleted
fixture modules); speedbump green (2 `Chan*` modules with triples,
both pinned); statement-TCB 48 byte-identical; full differential
re-run at the tip (entry below).
