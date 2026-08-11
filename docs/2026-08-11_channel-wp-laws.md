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

**NIL-CHANNEL ops.** A nil send/recv parks as
`.blockedSend/Recv none …`; `wakeReady` is never true and no
`applyPairing` arm matches a `none` loc — a nil-parked thread is
IRREDUCIBLE in the D-Language (and correctly so: the machine
deadlocks it). A WP over a nil-parked successor is unprovable at
NotStuck — which is honest: no law is stated for the nil park;
programs that reach it cannot get a triple through this pipe (they
have no `.normal` runs to speak about, so the vacuous-triple route is
closed off by the completion-pin half of the D1 pair). Recorded, not
worked around.

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
  (its law is witnessed separately by the sequential-degenerate probe
  below); this keeps the exemplar's law set exactly the rendezvous
  four + fork + loads.
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
3. `chanRendezvousTripleC : GoTripleC …` via `goTripleC_of_wpD` — the
   first frame-quantified triple whose program communicates on a
   channel across goroutines.
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

**The sequential-degenerate probe witness (`chanOpsProbe`)** for the
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

- **P-CL1-1 — buffered parked-sender law** (§3): needs the storeLoc
  round-trip lemma for the release construction at nonempty buffers.
  Course: law scoped to empty-buffer parks (covers cap-0). Consumer:
  buffered-park rows (slice 3).
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
  - **Gate**: full `scripts/ci --diff` run IN-LANE at this commit's
    tree (this worktree's first recorded differential — the
    documented fresh-checkout red; `GOLEAN_MEM_MAX=48G` per the
    parallel-lane cap discipline): **PASS, baseline diff FULL
    (1483/1483, no regression), negative lane no regression**,
    proofs + Audit green with the new registrations. Zero
    `GoLean/GoCore` edits anywhere in the slice — the differential
    surface is untouched by construction; the fresh run makes the
    zero-drift figure first-hand rather than argued.

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
