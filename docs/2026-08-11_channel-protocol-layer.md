# The channel protocol layer (channel-logic arc, slice 2)

Status: DESIGN OF RECORD for the slice, opened before building (the
binding discipline). Charter: `docs/2026-08-10_channel-logic-arc-charter.md`
work-plan item 2; predecessor record `docs/2026-08-11_channel-wp-laws.md`
(slice 1 — the law family, the phantom-pairing envelope §1a, the
parked-SELF-step/phantom-completion finding §8, the parking ledger
P-CL1-1..7). Branch `channel-logic-s2` off `channel-logic`. FD1–FD9
apply; latitude below is design latitude within FD2 (NATIVE
invariant+ghost at the iris-lean pin), decided here and recorded.
Everything in this slice is proofs-side (FD6): no machine change, no
new `Choices` site, no envelope change, zero corpus effect.

## 1. THE CENTRAL FINDING: on `StepDC`, NO ghost protocol can pin a
## delivered value — the ghost tie REQUIRES a mediated carrier

Slice 1 recorded the constraint (P-CL1-1/§8): a `pairRelease`
completion carries no delivery information, so value transfer must be
ghost-tied, never control-flow-inferred. Designing that ghost tie for
this slice ran into a stronger fact, provable from the adequacy
architecture itself, which reshapes the layer:

**Claim.** Over `LangD` (`StepDC`, `PoolCfgD`), no WP — with any
invariant, any ghost state constructible in the logic — can prove a
postcondition that pins a delivered channel value (e.g. "the receive's
target cell holds 42" when some sender sent 42).

**Why.** `StepDC.pairArrive` ∃-quantifies the partner pool: from any
open-channel receive apply position there is a Language step
delivering ANY value `v` — state unchanged, justified by an imagined
pool containing a `.blockedSend _ v _` partner (`applyPairing`'s
partner patterns wildcard everything the real pool would pin). These
phantom steps are REAL steps of the Language: the adequacy theorem
(`goD_heap_adequacy_own` → `adequate_result`) quantifies over every
erased Language trace, including a trace in which main receives 7,
stores 7, and terminates. A provable WP forces the postcondition to
hold at that trace's endpoint — where the target cell holds 7 — so a
42-pinning postcondition makes the WP UNPROVABLE. Ghost state cannot
help: the phantom step touches no interpreted state (the state interp
covers the physical heap only; the successor differs from the real one
only in the value riding the successor CONFIGURATION), so at the
`wp_lift_step` step-case the prover holds identical resources in the
real and phantom branches and can refute neither. This is not a
weakness of any particular law statement; it is a property of the
Language's step relation.

Consequence, recorded as the slice's governing decision: **the value
protocol lives on a NEW proof-layer per-thread Language whose channel
communication is CELL-MEDIATED** — every delivered value transits the
physical channel cell, where the state interpretation (and hence an
Iris invariant) can see it. This is exactly the O1(b) refinement the
decomposition note (`docs/2026-08-10_gospecc-decomposition.md` §3
options O1) recorded as "the refinement the channel WP law family may
prefer", and slice 1's §1a pre-authorized as "a fresh Language wrapper
if slice 2 wants it". Slice 2 wants it; the wrapper lands beside
`LangD` (which is untouched — the slice-1 laws remain the primitive
no-protocol tier, their carrier and exit unchanged).

Perennial cross-check (shape reference, both directions): their model
never has our problem because it is cell-mediated BY CONSTRUCTION —
GooseLang channel state is physical, blocking is a spin loop over it,
and `own_chan`'s ghost tracks the physical buffer through an
invariant. Our slice-1 carrier decomposed the machine's two-thread
pairing into per-thread steps with ∃-quantified partners instead —
sound, cheap for the simulation, and (now proved by use) incapable of
carrying a value protocol. The mediated carrier converges with their
architecture at exactly the point their architecture is load-bearing.

## 2. The mediated carrier (`StepDM`, `PoolCfgDM`, `LangDM.lean`)

### 2a. Design constraints, measured from the machine

- `coerceStoredValue old new` is IDENTITY on `.chanData` news (no arm
  matches a `chanData` new except the catch-all `| _, value => return
  value`), and `normalizeValueForTyFuel` is
  SUCCESS-IMPLIES-IDENTITY on `.chanData` (every arm matching a
  `chanData` value either fails closed or returns it unchanged —
  `.interface`/catch-all arms are `return value`; the `.defined` chain
  recurses; proved as `normalize_chanData_id` below). So a machine
  `storeLoc` that SUCCEEDS on a `chanData` value writes it verbatim.
- `Heap.set` is in-place replace on the association list, so
  `set (set h l c₁) l c₂ = set h l c₂` and
  `lookup h l = some c → set h l c = h` are cheap list inductions —
  the storeLoc ROUND-TRIP family P-CL1-1 named, at `.base` locations.
- Machine-allocated channels live at `.base` cells (`makeChan` →
  `ExecState.alloc`), but adversarial `InitialSplit` heaps can seed
  channel values whose `Loc` is a path (`.field`/`.index`). Path
  round-trips would drag `normalizeStructValueWith` equivalences in;
  the mediated rules are therefore scoped to `.base` cells and the
  ∃-style rules are KEPT for the non-base residue (restricted so they
  cannot fire at `.base`-parked plain shapes — the poison check in
  §2c). No law this arc states is about a path-loc channel.

### 2b. The rule set

`StepDM : Config → ExecState → Config → ExecState → List Config →
Prop`, wrapper `PoolCfgDM` (one-field, so the Language instance
coexists with `PoolCfg`/`PoolCfgD`):

1. `lift` — `StepE` verbatim (sequential steps incl. the cell-path
   channel/select applies, spawn).
2. `strip` — the `.spawned` marker strip.
3. `wake` — `resumeThread`, verbatim (machine function; reads only
   shared state + own config).
4. `sendDeposit` — an arriving plain SEND at its apply position over a
   `.base`-loc OPEN cell pushes its normalized value into the buffer
   CAP-RELAXED (no room check) and completes to `.next k`. Raw cell
   write (`Heap.set`, `declaredTy` preserved).
5. `parkedSendDeposit` — a parked plain sender (`.blockedSend (some
   (.base a)) v' k`) at an open cell pushes cap-relaxed and completes.
6. `recvDrain` — an arriving plain RECV at its apply position over a
   `.base`-loc cell with `buf = v ⋯` dequeues RAW and enters the
   machine's own delivery (`resumeRecvDelivery`-shaped successor with
   `(v, true)`).
7. `parkedRecvDrain` — the parked twin of 6.
8. `selSendDeposit` / `parkedSelSendDeposit` — a select (at its apply
   position resp. parked as `.blockedSelect evs env k`) with a send
   clause `evs[ci] = .sendEv chv vv elem body` on an open `.base`
   cell pushes the commit-normalized value cap-relaxed and proceeds to
   `.exec body env k`. The apply-position form carries the
   ∃-pool `arrivalCases` evidence pinning `evs` (which is a function
   of σ and the config's own operands — value-clean even though the
   pool is imagined).
9. `selRecvDrain` / `parkedSelRecvDrain` — the recv-clause twins:
   dequeue raw, `selectRecvDelivery`-shaped successor with the HEAD.
10. `pairArriveNB` — `StepDC.pairArrive` verbatim PLUS the hypothesis
    that the pairing's cell loc (`pairLoc bc cand` — the would-block
    shape's loc, resp. the arriving select clause's `chanValueLoc`)
    is NOT `.base`.
11. `pairReleaseNB` — `StepDC.pairRelease` restricted to parked
    shapes that are `.blockedSend` (whose release projection is
    provably pure control `.next ks` in every arm —
    `applyPairing_partner_write`; the phantom COMPLETION stays, see
    the poison check), `.blockedSelect` (select laws are deferred
    P-CL1-2; the ∃-release for parked selects is recorded as this
    carrier's remaining wide spot), or a `.blockedRecv` whose OWN loc
    is NOT `.base`. A parked plain receiver on a `.base` cell has NO
    ∃-release — its only completions are `wake` and `parkedRecvDrain`,
    both delivering the CELL HEAD.
12. `selCommitCell` — `StepDC.selCommit` verbatim (`commitClause`
    against the real cell; value-clean by construction).

### 2c. The poison check (what the laws may rely on)

For the shapes this slice ships laws about — plain send/recv apply
positions and plain parked shapes over `.base` cells:

- a RECEIVE (arriving or parked) can complete ONLY by `lift`
  (cell-path dequeue / closed-zero / park), `wake` (drain/closed-zero)
  or `recvDrain`/`parkedRecvDrain` — in every delivering branch the
  value IS the physical buffer head. **No step delivers an
  un-interpreted value.** This is what makes the Ψ-protocol sound.
- a SEND (arriving or parked) completes by `lift`-enqueue, `wake`-push,
  or the deposit rules — every completion WRITES the value into the
  buffer... with ONE exception: `pairArriveNB` cannot fire (loc is
  `.base`), but a parked plain sender still has `pairReleaseNB`'s
  pure-control phantom completion (imagined pairing elsewhere). The
  send-side tie "completed ⇒ value entered the buffer" therefore holds
  for the ARRIVING send's law but NOT for the parked sender, whose law
  keeps the phantom-completion branch. Recorded consequence: the
  send-side ghost obligations are stated at the deposit branches only,
  and nothing this slice exports infers delivery from a parked
  sender's completion (unchanged slice-1 doctrine). Removing the
  parked-sender phantom too would need dropping `.blockedSend` from
  rule 11 and mediating the remaining non-base residue — recorded as
  the successor refinement (P-CL2-2 below), not needed by the
  receiver-side value pinning this slice's exports rest on.
- parked configurations at empty open cells are IRREDUCIBLE (no spin
  rules — the slice-1 Löb machinery is not needed here). The exit
  therefore runs at `.MaybeStuck` (iris-lean's `adequate`,
  `adequate_alt`, `wp_strong_adequacy_gen` are stuckness-generic —
  verified at the pin), and `adequate_result` — the only field the
  exit consumes — is stuckness-independent. No exported statement
  mentions stuckness (deletion test unchanged); pool no-stuckness was
  already recorded as silent on deadlock (decomposition note §3 O2),
  so nothing weakens.

### 2d. The simulation (`stepM_erasedDM`)

Every `StepM` step maps to 1–2 erased DM-steps.
`thread`/`spawned`/`wake`/`pickCommit` are verbatim (rules 1/2/3/12).
The pairing arms decompose DEPOSIT-THEN-DRAIN (the §2 attribution of
the decomposition note replaced by genuine mediation — both
directions' intermediate state is the pushed cell, a state the machine
never exhibits at cap 0; sound because the exports quantify `execProg`
alone, exactly the slice-1 envelope argument):

| machine arm (`applyPairing`) | step 1 (deposit) | step 2 (drain) |
|---|---|---|
| arriving send × parked recv (empty buf) | `sendDeposit(i)` | `parkedRecvDrain(j)` |
| arriving send × parked select recv-clause | `sendDeposit(i)` | `parkedSelRecvDrain(j)` |
| arriving recv × parked send (empty) | `parkedSendDeposit(j)` | `recvDrain(i)` |
| arriving recv × parked send (nonempty: head-and-refill) | `parkedSendDeposit(j)` | `recvDrain(i)` — `(buf.push v).eraseIdx 0 = (buf.eraseIdx 0).push v` |
| arriving recv × parked select send-clause | `parkedSelSendDeposit(j)` | `recvDrain(i)` |
| arriving select recv-clause × parked send | `parkedSendDeposit(j)` | `selRecvDrain(i)` |
| arriving select send-clause × parked recv | `selSendDeposit(i)` | `parkedRecvDrain(j)` |
| any arm at a NON-`.base` cell loc | `pairArriveNB(i)` | `pairReleaseNB(j)` |

Endpoint equality per arm: the deposit's raw push then the drain's raw
dequeue collapse by the round-trip kit
(`Heap.set` collapse/self + `normalize_chanData_id` where the machine
itself wrote via `storeLoc`), landing on the machine's `(ts', σ'')`
exactly. Provenance obligations: the partner's channel loc equals the
arriving loc — recovered from the waiter-scan membership inversions
(`recvSideWaiters`/`sendSideWaiters` membership; for select arrivals,
the `selectArrivalCases` inversion pinning `evs = evalClauses …` and
each candidate's clause/side). These inversions are the simulation's
main cost; they are pure, constructive, and land in the same module.

Run erasure, adequacy, and the exit (`execProg_erasedDM`,
`goDM_heap_adequacy_own`, `goTripleC_of_wpDM`) are structural
re-plumbs of the LangD versions (the erasure induction and the
adequacy ghost construction do not mention the rule set's content).

## 3. The protocol layer over the mediated carrier

### 3a. What the invariant owns

Tier 1, SHIPPED this slice (the exemplar's consumer):

    chanInvΨ (a : Addr) (dt) (cap) (Ψ : GoValue → IProp) : IProp :=
      ∃ buf, a.id ↦ ⟨dt, .chanData buf cap false⟩
             ∗ [∗list] v ∈ buf.toList, Ψ v

`is_chanΨ N a dt cap Ψ := Iris.inv N (chanInvΨ a dt cap Ψ)` —
persistent, shareable across the fork. The invariant owns the physical
cell AND the per-element value protocol; the OPEN (`closed = false`)
shape is pinned (close-protocols are tier 2). What send and recv
atomically exchange, stated as the laws' obligations:

- **send/deposit**: to complete, the sender re-establishes the
  invariant with the PUSHED buffer — it must GIVE `Ψ v'` for its
  normalized value. (The enqueue branch via `lift` and the deposit
  branch write the same cell at dt-pinned invariants —
  `coerceStoredValue` identity — so both branches carry one
  obligation.)
- **recv/drain**: the receiver opens the invariant, observes
  `buf = v :: rest`, TAKES `Ψ v`, and re-establishes with `rest`. The
  continuation is `∀ v, Ψ v -∗ WP (deliver v)` — value knowledge
  enters the walk; with `Ψ v := ⌜v = .int 42 .int⌝` the delivered
  value is PINNED.
- parked twins: identical exchanges at the wake/drain branches; the
  parked sender additionally absorbs the phantom-completion branch
  (§2c) with no exchange (state unchanged, nothing learned — the
  honest residue, stated in the law's docstring).

### 3b. Ghost state: what this slice does and does not build (FD9)

The pin carries GhostMap/Auth/FracAuth/ExclAuth/Frac/DFrac/Excl/Agree.
Tier 1 needs NONE of them beyond the invariant machinery itself: the
exemplar's protocol is a pure per-element predicate, and shipping an
auth-ghost "logical contents" (`own_chan γ (contents)`) without a
consumer would be exactly the scaffold the non-vacuity discipline
forbids. Options recorded:

- (a) **pure-Ψ per-element invariant (TAKEN)** — consumer: the
  value-pinning exemplar; covers every protocol expressible as a
  per-message predicate (incl. the fork/join 42 class and singleton
  session shapes).
- (b) **auth/frag logical-contents ghost (`own_chan`-style; DESIGNED,
  recorded as P-CL2-3, folding in slice 1's P-CL1-3)** — the
  invariant owns `auth γ buf` beside the cell; the client owns
  `frag γ` views; send/recv become HoCAP atomic updates against the
  logical state, DERIVED over the tier-1 accessor laws (never
  restating them). First consumers: close-protocols (a closed flag in
  the logical state), buffered histories, and the dsp/muxer session
  rows. Constructions available at the pin per FD9; a mono-list or
  saved-prop convenience, if one turns out missing, is built locally
  and recorded.

### 3c. The law family (shipped forms)

On the DM-carrier, prefix `wpDM_*`; house obligations unchanged (FD7
axioms, same-commit witnesses, Audit registration, docstrings scoped
to what the witness demonstrates). Stuckness: laws stated `@ s` where
provable generically; the parked-receive law and the exemplar walk at
`.MaybeStuck` (§2c). Planned set — the D-ports of the kit
(`wpDM_pure_det`, `wpDM_spawned_strip`, `wpDM_eval_var`,
`wpDM_fork`, `wpDM_fork_alloc₁`, a store law for the delivery frame)
plus the protocol laws:

- `wpDM_send_invΨ` — arriving send under `is_chanΨ`: branches
  {park (cap-full), enqueue (room), deposit} with one Ψ-obligation on
  the writing branches; rendezvous instantiation pins cap 0 so the
  enqueue branch is refuted.
- `wpDM_recv_invΨ` — arriving TARGETED receive (P-CL1-5 closes):
  branches {park (empty), drain (head, with `Ψ head`)}; zero-target
  degenerate included.
- `wpDM_blocked_send_invΨ`, `wpDM_blocked_recv_invΨ` — parked twins
  (wake/deposit resp. wake/drain branches; sender keeps the
  phantom-completion branch).
- CLOSE/len-cap/MAKE and the general-`S` forms: unchanged P-CL1-6/7
  status (owned-cell close already shipped slice 1 on the D-carrier;
  its DM sibling lands with a sharing consumer).
- SELECT laws: P-CL1-2 unchanged (deferred; the carrier's select
  rules exist for the SIMULATION, not as law targets).

## 4. The exemplar with values (work-plan item 3)

`chanRendezvousValProg` — the slice-1 exemplar with the receive
TARGETED: worker sends 42, main receives into `x` (pre-seeded int
cell); post pins BOTH the frame cells AND `x = 42`:

- pre: harness ∗ handle ∗ chanData ∗ x-cell; the chanData cell is
  surrendered to `is_chanΨ` with `Ψ v := ⌜v = .int 42 .int⌝` at the
  walk's head (Q loses the chanData cell — unchanged slice-1 cost).
- the walk: fork (`wpDM_fork_alloc₁`), send apply → {park →
  deposit/wake | deposit} with Ψ discharged at `.int 42 .int`
  (`rdvNorm42` reused); main recv apply → {park → wake-drain | drain}
  receiving `Ψ v`, hence `v = 42`; the delivery frame stores 42 into
  `x` (target-store steps, `wpDM_store` class); post carries
  `x ↦ 42`.
- `chanRendezvousValTripleC` via `goTripleC_of_wpDM` — **the claim
  slice 1 explicitly could not make**: run-conditioned, frame-
  quantified, "every `.normal` completion leaves `x = 42`".
- D1-BOTH: `chanRendezvousValReadoutC` (first-order readout at the
  seed, pinning the 42 in `loadLoc` vocabulary) +
  `chanRendezvousValTerminatesNormallyC` (seeded `allStreamsOkPool`
  kernel certificate, `#eval` first, `execProgLoop_mono` lift).
  Completion-pin convention observed (review-held; the name speedbump
  will see `ChanRendezvousVal`'s pair).

TCB-grounding walk (charter criterion): the trusted endpoints are
(i) the run-conditioned `execProg`/`loadLoc` readout — including the
42 pin — and (ii) the kernel-evaluated completion certificate; the
carrier, simulation, invariant, and Ψ-machinery are all proof-side
method (none appears in an exported statement; Iris deletion test per
statement). The grounding table lands in §8 with the build.

## 5. P-S4-1: ∀-heap `ProgressExecC` for the spawning witness

Independent of the carrier (pool-reachability lane). The spawn-noop
program's pool run is HEAP-BLIND: every configuration either thread
reaches steps without reading or writing the heap (`goStmtEntry`,
nullary callee eval, `spawnStep` with a no-arg/no-decl worker, seq
steps, empty `frameFall`), so from ANY admissible `InitialSplit`
state the reachable pool set is a finite set of thread-shape stages
over the CONSTANT shared state. The proof is an invariant induction
over `execProgLoop`:

- a stage predicate enumerating main's 5 configs × the child's
  absent/4 configs (with `cur` tracking);
- per stage: `stepMulti` computes (the L1 pick branches where two
  threads are runnable — both successors stay in the family),
  `raceUpdate` is conflict-free (empty footprints; the spawn edge is
  a pure clock op), the deadlock classifier never fires (no stage is
  blocked), and main's terminal stage exits `.ok (.normal σ₀ …)`;
- fuel induction gives: every run is `.ok (.normal …)` or
  `.error .fuelOut` — `ProgressExecC` at full `InitialSplit`
  strength; `spawnNoopSpecC := ⟨spawnNoopTripleC, ·⟩` assembles the
  S4 note's owed `GoSpecC`.

This is the pool-reachability kit's first instance deliberately built
CONCRETE (per-program stage enumeration) rather than as a generic
kit — the S4 note's §5 generic form grows from instances, not ahead
of them (the house anti-scaffold rule).

## 6. Flagship down-payment (work-plan item 5): HONEST DEFERRAL

All six charter rows (`dsp`, `muxer async/client`, the select-tricky
trio) contain `select` — measured at their pinned lowerings — so a
compositional re-proof needs the select law family (P-CL1-2,
explicitly deferred by slice 1 with slice-3 consumers named) on top of
this slice's carrier, plus (for dsp/muxer) loop-invariant machinery.
Per the charter's exemplar-first discipline ("an honest smaller row or
a recorded deferral beats a stall"), the down-payment this slice makes
is the CARRIER + VALUE LAYER itself — the machinery every row's
delivered-value verdict was blocked on — with `chanRendezvousValTripleC`
as its exemplar row, and the flagship re-proof is DEFERRED to slice 3
with its prerequisite chain named: DM-carrier select laws (P-CL1-2 on
the new carrier) → per-row invariants → dsp. Ledger entry P-CL2-4.

## 7. Parking ledger (slice 2)

- **P-CL2-1 — path-loc mediated rules**: the ∃-rules 10/11 remain for
  non-`.base` channel cells (adversarial-seed residue; no law targets
  them). Course: mediate if a law ever needs a path-loc channel
  (none foreseen — machine-made channels are `.base`).
- **P-CL2-2 — parked-sender phantom completion** (§2c): remains in
  rule 11 (`.blockedSend` arm). Course: laws state send-side ghost
  obligations at deposit branches only. Consumer for removal: a law
  needing "parked sender completed ⇒ delivered" — none shipped, none
  planned (receiver-side pinning suffices for the arc's rows).
- **P-CL2-3 — the auth-ghost `own_chan` tier + HoCAP au-forms**
  (§3b(b); folds in P-CL1-3): derivation over the tier-1 laws when a
  close-protocol/history consumer lands (dsp's session row is the
  named candidate).
- **P-CL2-4 — flagship re-proof** (§6): deferred to slice 3 behind
  the DM select laws; the trio/dsp/muxer rows remain on their
  certificate families meanwhile (unchanged headline).
- **P-CL2-5 — parked-select ∃-release** (§2b rule 11): parked selects
  keep the wide ∃-release envelope on this carrier. Course: no select
  laws this slice; the select law family (P-CL1-2) must either
  mediate the parked-select residue or absorb it, decided when built.
- **P-CL1-1 (updated)**: the storeLoc round-trip family ships HERE
  (base-loc form) as the simulation kit; the buffered parked-sender
  law's honest statement ("value entered the buffer") becomes
  makeable on the DM-carrier for the deposit/wake branches — the
  buffered law forms land with their slice-3 consumers, per P-CL1-7.

## 8. Build log (appended as built)

(opened with the note; entries land per commit)
