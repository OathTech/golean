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
Language's step relation. EPISTEMIC STATUS (stated per the S2 audit
fix round): this is a rigorous INFORMAL argument over the
empty-buffer `pairArrive` arm — unmechanized; no Lean theorem states
or proves the impossibility. What is mechanized is the constructive
side: the mediated carrier exists and the value-pinning exemplar goes
through on it. The claim's role is to record why the carrier was
built, not to serve as a trusted artifact.

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
   `.exec body env k`. [ALIGNED with the shipped constructor at the
   S2 audit fix round: the apply-position form pins `evs` by a direct
   `evalClauses clauses ((v :: done).reverse) = .ok evs` hypothesis —
   a function of σ and the config's own operands; the drafted ∃-pool
   `arrivalCases` formulation was not what shipped.]
9. `selRecvDrain` / `parkedSelRecvDrain` — the recv-clause twins:
   dequeue raw, `selectRecvDelivery`-shaped successor with the HEAD.
10. `pairArriveNB` — `StepDC.pairArrive` verbatim PLUS the hypothesis
    that the pairing's cell loc (`pairLoc bc cand` — the would-block
    shape's loc, resp. the arriving select clause's `chanValueLoc`)
    is NOT `.base`.
11. `pairReleaseNB` — `StepDC.pairRelease` restricted by
    `parkedReleaseNB`. [AMENDED AT BUILD, stronger than drafted: the
    draft kept `.blockedSend` in the release with its phantom
    completion; the build EXCLUDES `.base`-parked plain SENDS too —
    the simulation never needed their release (every machine arm with
    a `.base`-parked sender is mediated via `parkedSendDeposit`), so
    both plain parked shapes on `.base` cells have NO ∃-rule, no
    self-step, no Löb, and the send-side tie "completed ⇒ value
    physically in the buffer" HOLDS (P-CL2-2 resolved stronger; the
    old P-CL1-1 statement becomes a law-level fact).] Kept for:
    `.blockedSelect` (select laws deferred, P-CL2-5), non-`.base` and
    nil parks (no law targets them).
12. `selCommitCell` — `StepDC.selCommit` verbatim (`commitClause`
    against the real cell; value-clean by construction).

### 2c. The poison check (what the laws may rely on)

For the shapes this slice ships laws about — plain send/recv apply
positions and plain parked shapes over `.base` cells:

- a RECEIVE (arriving or parked) can complete ONLY by `lift`
  (cell-path dequeue / closed-zero / park), `wake` (drain/closed-zero)
  or `recvDrain`/`parkedRecvDrain` — and in every delivering branch
  **of an OPEN cell** the value IS the physical buffer head. [SCOPED
  at the S2 audit fix round — the first form said "every delivering
  branch", which is false for the two closed-zero branches this very
  bullet lists: on a CLOSED empty cell both `lift`'s cell path and
  `wake` deliver `defaultValue σ elem`, NOT a head. What makes the
  shipped Ψ-protocol sound is the CONJUNCTION of head-delivery and
  `chanInvP`'s pinned `closed = false`, which refutes the closed-zero
  branches — the pin is LOAD-BEARING. Forward warning for the tier-2
  close-protocol successor (P-CL2-3): the moment the pin is dropped,
  the closed-zero branches reopen with a value (`defaultValue`) that
  need not satisfy Ψp — a close-protocol law must handle them
  explicitly, never inherit this bullet's open-cell reasoning.]
- a SEND (arriving or parked) completes by `lift`-enqueue, `wake`-push,
  or the deposit rules — every completion WRITES the value into the
  buffer, with NO exception on this carrier: `pairArriveNB` cannot
  fire at a `.base` loc, and `.base`-parked plain sends are excluded
  from `pairReleaseNB` (rule 11 as SHIPPED — the build amendment; the
  first form of this bullet still described the drafted rule set with
  its parked-sender phantom completion and was corrected at the S2
  audit fix round, finding: the note contradicted its own §2b/§7
  amendment records). The send-side tie "completed ⇒ the value is
  physically in the buffer" holds for BOTH send laws
  (`wpDM_send_invP`, `wpDM_blocked_send_invP` — the successor set is
  exactly park-or-push resp. push).
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
- parked twins: identical exchanges at the wake/drain branches.
  [CORRECTED at the S2 audit fix round: the drafted "parked sender
  additionally absorbs the phantom-completion branch" clause described
  the pre-amendment rule set — on the SHIPPED carrier `.base`-parked
  plain sends have no ∃-release (§2b rule 11), the parked-send law's
  successor set is exactly the push, and its docstring says so.]

### 3b. Ghost state: what this slice does and does not build (FD9)

The pin carries GhostMap/Auth/FracAuth/ExclAuth/Frac/DFrac/Excl/Agree.
Tier 1 needs NONE of them beyond the invariant machinery itself: the
exemplar's protocol is a pure per-element predicate, and shipping an
auth-ghost "logical contents" (`own_chan γ (contents)`) without a
consumer would be exactly the scaffold the non-vacuity discipline
forbids. Options recorded:

- (a) **pure-Ψ per-element invariant (TAKEN, and shipped PURE:
  `Ψp : GoValue → Prop` — the §8 commit-4 amendment reaches this
  design text)** — consumer: the value-pinning exemplar; covers every
  protocol expressible as a per-message PURE predicate (the fork/join
  42 class and value-pinned singleton shapes). CAPABILITY LIMIT,
  stated (S2 audit fix round): a pure predicate holds no resources —
  it can pin a message's identity but cannot transfer OWNERSHIP with
  it (sending a pointer does not move its points-to), which is the
  defining move of a channel session protocol and exactly what the
  dsp flagship needs (§6 obstacle 1). Protocols needing resource
  transfer take the `IProp`-valued per-element form or tier (b) —
  both in P-CL2-3, with dsp the named consumer.
- (b) **the resource-carrying successors (P-CL2-3, folding in slice
  1's P-CL1-3)** — two forms, in order: the `IProp`-valued
  per-element invariant (`Ψ : GoValue → IProp`, the `[∗list]` form
  §3a originally sketched — deposit folds the sender's resource in,
  drain hands it out: OWNERSHIP TRANSFER with the message), and the
  auth/frag logical-contents ghost (`own_chan`-style: the invariant
  owns `auth γ buf`, clients own `frag γ` views, send/recv become
  HoCAP atomic updates DERIVED over the tier-1 accessor laws, never
  restating them). First consumers: the dsp session row (§6 —
  pointer-passing needs the transfer), close-protocols (a closed flag
  in the logical state; §2c's forward warning applies), buffered
  histories. Constructions available at the pin per FD9; a mono-list
  or saved-prop convenience, if one turns out missing, is built
  locally and recorded.

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
  (wake/deposit resp. wake/drain branches; no ∃-release exists for
  either on the shipped carrier — §2b rule 11 [corrected at the S2
  audit fix round; the drafted "sender keeps the phantom-completion
  branch" clause was pre-amendment]).
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

## 6. Flagship down-payment (work-plan item 5): deferral RE-GROUNDED
## at the S2 audit fix round — the first recorded reason was FALSE

[REWRITTEN at the S2 audit fix round. The section's first form claimed
"all six charter rows contain `select` — measured at their pinned
lowerings", inside a quotation attributed to the charter that does not
appear in it. Both were wrong — the audit's confirmed MAJOR:
`selectStmt` counts at the pinned lowerings are ImportedGooseActris
**0**, ImportedGooseMuxer **0**, ImportedGooseSelectTricky **4**
(`Stmt.while`: Actris **0**, Muxer **3**, SelectTricky **0**) —
re-measured first-hand at this round. dsp has neither a select nor a
loop; the select-law prerequisite chain the first form recorded for it
was fabricated by sloppy generalization from the trio. The fix
directive was to ATTEMPT dsp; the attempt's outcome follows.]

**The dsp attempt (this round), and where it actually blocks.** dsp's
lowering (`Specs/ImportedGooseActris.lean`; upstream `DSPExample`,
Actris 2.0 prog3) is: `make(chan any)` ×2, a goroutine whose body is
`ptr := (<-c).(*int); *ptr = *ptr + 2; signal <- struct{}{}`, and a
main path `ptr := new(40); c <- ptr; <-signal; return *ptr`. Statement
inventory (measured): assign ×5, assignMany, block ×3, call,
chanRecv ×2, chanSend ×2, goStmt, initialization ×9, makeChan ×2,
newValue, returnStmt ×2 — no select, no loop. Two genuine obstacles,
in order of depth:

1. **The protocol is a RESOURCE-TRANSFER session, which the shipped
   pure-Ψp tier provably cannot express.** The message on `c` is a
   POINTER whose pointed-to cell the RECEIVER must then write
   (`*ptr = *ptr + 2`) and the sender later read back
   (`return *ptr`) — the walk's child-side store step needs
   `x ↦ 40` at the child, then `signal` must carry `x ↦ 42` back to
   main. `Ψp : GoValue → Prop` can pin the pointer's IDENTITY but
   cannot carry the points-to with the message (a pure predicate
   holds no resources); main cannot keep the cell either (the child's
   `wpDM_store_step` needs it). The attempt blocks at exactly the
   child's store, with no law to apply. This is the capability limit
   §3b now states, and it makes dsp the NAMED FLAGSHIP CONSUMER of
   the `IProp`-valued per-element tier (resource-carrying Ψ; the
   `[∗list]` invariant form) recorded in P-CL2-3 — the audit's
   downgraded-to-note pure-Ψ finding anticipated precisely this.
2. **The wpDM sequential-law surface**: the row's walk additionally
   needs DM ports with no shipped counterpart — the allocating cores
   (block/`initialization` via `allocDecls`, `makeChan` — P-CL1-6,
   still unshipped on any carrier — `new`, call-frame entry/exit with
   result stores) plus the typeAssert/assignMany store walks. All
   mechanical (the S1→S2 port pattern), none present.

Neither obstacle is the select law family, and neither is a loop. The
muxer `client` row (the one row with a live loop, via `Serve`'s
`for { s.res <- f(<-s.req) }`) additionally needs loop-invariant
machinery; `async` needs neither select nor loop. The trio remains
the only select consumer of P-CL1-2.

**Disposition (unchanged conclusion, corrected grounds):** the
flagship re-proof is DEFERRED to slice 3 with the TRUE prerequisite
chain — the resource-carrying Ψ tier (P-CL2-3, dsp now its named
consumer) + the wpDM allocating/call/typeAssert law ports → dsp; the
down-payment this slice makes is the carrier + value layer with
`chanRendezvousValTripleC` as its exemplar row. Ledger entry P-CL2-4,
re-grounded. Charter basis for the deferral latitude: the standing
goal's deferral clause (charter "The standing goal": "goals deferred
for good reason and logged — deferral with an honest log entry is
SUCCESS") — the previous form's quotation marks around invented
charter text are withdrawn.

## 7. Parking ledger (slice 2)

- **P-CL2-1 — path-loc mediated rules**: the ∃-rules 10/11 remain for
  non-`.base` channel cells (adversarial-seed residue; no law targets
  them). Course: mediate if a law ever needs a path-loc channel
  (none foreseen — machine-made channels are `.base`).
- **P-CL2-2 — parked-sender phantom completion: RESOLVED STRONGER AT
  BUILD** (§2b rule 11 amendment): `.base`-parked plain sends are
  excluded from the ∃-release entirely — the simulation mediates every
  arm they appear in — so the send-side tie holds as a law
  (`wpDM_blocked_send_invP`'s successor set is exactly the push).
- **P-CL2-3 — the resource-carrying Ψ tiers** (§3b(b); folds in
  P-CL1-3): the `IProp`-valued per-element invariant (ownership
  transfer with the message) and the auth-ghost `own_chan` tier +
  HoCAP au-forms, derived over the tier-1 laws. NAMED FLAGSHIP
  CONSUMER (S2 audit fix round): the dsp row — its pointer-passing
  session provably exceeds pure Ψp (§6 obstacle 1); close-protocols
  and buffered histories follow (§2c's closed-zero forward warning
  applies to the close tier).
- **P-CL2-4 — flagship re-proof: RE-GROUNDED at the S2 audit fix
  round** (§6 — the first entry's "behind the DM select laws" chain
  was FALSE for dsp/muxer, the audit's confirmed major; dsp has no
  select and no loop, measured): deferred to slice 3 behind the TRUE
  chain — resource-carrying Ψ tier (P-CL2-3) + the wpDM
  allocating/call/typeAssert law ports → dsp; muxer `client`
  additionally the loop machinery; the trio (the only select
  consumer) behind P-CL1-2. The six rows remain on their certificate
  families meanwhile (unchanged headline).
- **P-CL2-5 — parked-select ∃-release** (§2b rule 11): parked selects
  keep the wide ∃-release envelope on this carrier. Course: no select
  laws this slice; the select law family (P-CL1-2) must either
  mediate the parked-select residue or absorb it, decided when built.
- **P-CL1-1 (updated)**: the storeLoc round-trip family ships HERE
  (base-loc form) as the simulation kit; the buffered parked-sender
  law's honest statement ("value entered the buffer") becomes
  makeable on the DM-carrier for the deposit/wake branches — the
  buffered law forms land with their slice-3 consumers, per P-CL1-7.

- **P-CL2-6 — constructivize the beq-reflexivity route (RE-MEASURED
  at the S2 audit fix round — the first entry's root cause was
  WRONG)**: the classical carrier is NOT String/Int beq lawfulness
  (`instLawfulBEqString` is axiom-free; `Int.instLawfulBEq` is
  `[propext, Quot.sound]` — measured). It is the `BEq.rfl` route the
  GoLean instance proofs' `simp` takes: `ReflBEq` resolves through
  `EquivBEq.toReflBEq ∘ Std.LawfulBEqOrd.equivBEq` over
  `Nat.instLawfulEqOrd`/`Nat.instTransOrd`, and those two core Ord
  instances carry `Classical.choice`. Not Loc-specific: `LawfulBEq
  Addr` (Nat-only) is equally classical; the DM kit and simulation
  inherit it through every `Heap.set`/`Heap.lookup` beq-if reduction
  and scan `eq_of_beq`. This is a RECORDED DEVIATION from FD7's
  constructive-simulation-lane clause (labeled at the Audit block and
  §9's FD7 line): the enforced axiom registrations are accurate, the
  deviation is disclosed, and the fix is either constructivizing the
  two instance `rfl` fields away from `BEq.rfl` or routing the kit
  around beq. No soundness content; the LangD lane unchanged.

## 8. Build log (appended as built)

- **Commit 1** — this note.
- **Commit 2 — THE MEDIATED CARRIER** (`proofs/GoLeanProofs/LangDM.lean`,
  ~2350 lines; Audit block + root import). Everything of §2 built:
  the raw-cell round-trip kit (P-CL1-1's family at `.base` scope, incl.
  `normalize_chanData_id` — the normalizer's success-identity on
  channel payloads, which is what lets machine `storeLoc` writes
  factor through raw `Heap.set`), `StepDM` + Language instance, the
  waiter-scan/arrival-analysis provenance inversions (the
  `selectArrivalCases` mapM walk included), the DEPOSIT-then-DRAIN
  pairing simulation over all six machine arms (+ the non-`.base`
  ∃-residue via the restricted rules), run erasure, `.MaybeStuck`
  adequacy, THE EXIT `goTripleC_of_wpDM`, and the ported `wpDM` kit
  incl. the STORE core. In-build decisions, recorded: the rule-11
  strengthening (§2b amendment — P-CL2-2 resolved stronger); the
  `.MaybeStuck` exit confirmed available at the pin (`adequate`,
  `adequate_alt`, `wp_strong_adequacy_gen` all stuckness-generic);
  the Loc-beq classical finding (P-CL2-6). RECORDED BLEMISH: commit 2
  is not self-contained as a checkout — its root-import edit also
  carried the (then-untracked-file) import line for commit 3's module;
  the branch tip builds, intermediate-commit bisection over exactly
  commit 2 does not. `scripts/ci` green at the commit.
- **Commit 3 — P-S4-1 PAID** (`Specs/SpawnNoopProgress.lean`, built by
  a delegated Fable worker to the note's §5 route; reviewed): ∀-heap
  `ProgressExecC` for the spawning witness by heap-blind stage-family
  invariant induction over `execProgLoop` — no Iris, no kernel
  enumeration — plus `spawnNoopSpecC` (the S4 note's owed
  `GoSpecC` assembly) and `spawnNoopPoolProgress`, the same fact in
  interpreter vocabulary at the CONSTRUCTIVE set (the `ProgressExecC`
  form inherits `Classical.choice` from the surface statement
  vocabulary itself — `InitialSplit`/`sat`/`heapletOf` over
  `PartialMap` — a pre-existing property, measured and recorded at
  the Audit block). `scripts/ci` green.
- **Commit 4 — THE PROTOCOL LAWS + THE VALUE-PINNING EXEMPLAR**
  (`ChanDM.lean`, `Specs/ChanRendezvousVal.lean`; Audit block + root
  import). Decision recorded, AMENDING §3a's sketch: the shipped
  tier-1 invariant `chanInvP` carries the per-element protocol as a
  PURE predicate (`Ψp : GoValue → Prop`) rather than the sketched
  `[∗list]` of `IProp`s — the exemplar's protocol is pure, a pure Ψ
  makes every branch obligation a plain hypothesis/pure-disjunction
  (no big-op machinery), and shipping the `IProp` form without a
  consumer is the scaffold smell; the `IProp` per-element form joins
  the auth-ghost tier in P-CL2-3 as the recorded growth path. Also
  pinned: `declaredTy = none` (the machine-real `makeChan` shape, the
  S1 close-law precedent) and the OPEN cell. The four laws shipped
  (`wpDM_send_invP`, `wpDM_blocked_send_invP`, `wpDM_recv_invP` —
  P-CL1-5 closed, `wpDM_blocked_recv_invP` — the one
  `.MaybeStuck`-fixed member), each consumed same-commit by the
  exemplar: `chanRendezvousValTripleC` — **the claim slice 1 could
  not make**: every `.normal` completion from any admissible seeded
  heap leaves `x = 42`, proved compositionally (fork → send-under-Ψ
  → receive-under-Ψ → delivery-frame store walk → exit). Figures
  (measured): cert fuel 500, `#eval`-confirmed `true` before
  `decide +kernel` (with the seed's `MachineWf` decide eval'd too);
  walk under `maxHeartbeats 3200000`; axiom sets FD7-exact
  (laws/witness/exit classical trio; cert `[propext, Quot.sound]`;
  pure helpers `[propext]`); the completion-pin speedbump sees 3
  `Chan*` modules, all pinned. `scripts/ci` green.
- **The differential record at the slice tip** [CORRECTED at the S2
  audit fix round — the debt recorded here is PAID]: every commit ran
  `scripts/ci` green; the fresh clean-tree full differential this
  entry first recorded as owed was RUN BY THE AUDIT at the slice tip
  `f743a677` — **PASS, zero drift**, and its record is the current
  `artifacts/coverage/latest.meta.tsv`: `git_commit
  f743a677847f6ee99bc78870c190a044908c0824`, `git_dirty false`,
  `manifest_cases 1483`, `manifest_sha256 5dd06a6c…17e4733` (read back
  first-hand at this round). Commit shas for the record (and the
  bisection cross-reference): commit 1 `4e6aa717`, commit 2
  `04008ff1` (the non-self-contained one — see the blemish note in
  its entry above), commit 3 `b7c39858`, commit 4 `5a1699bb`,
  discharge record `f743a677`.

## 9. The TCB-grounding walk (the per-slice review criterion)

| exported artifact | (i) trusted endpoint (interpreter vocabulary) | (iii) executable anchor |
|---|---|---|
| `chanRendezvousValTripleC` | ∀ admissible seeded heap, run-conditioned: `execProg … = .ok (.normal σf, _)` → harness/handle intact ∧ `loadLoc σf x = .ok (.int 42 .int)` | run-conditioned only — anchored by the pin row below (the standing `ChanVacuityWarning` demonstration) |
| `chanRendezvousValReadoutC` | the same, first-order at the concrete seed — **the 42 pin in `loadLoc` vocabulary** | premises discharged at the seed; consumes the triple as method |
| `chanRendezvousValTerminatesNormallyC` | ∃N ∀fuel≥N ∀ch: `.normal` completion | `chanRendezvousValAllStreamsCert` — kernel evaluation (fuel 500, `#eval` first), `execProgLoop_mono` lift |
| `spawnNoopProgressC` / `spawnNoopSpecC` / `spawnNoopPoolProgress` | ∀ heap/allocator, ∀ fuel/stream: `execProg` is `.ok (.normal …)` or `.error .fuelOut` (and the `GoSpecC` conjunction) | the invariant induction is itself interpreter-side (no Iris anywhere in statement OR proof for the progress half) |

## 9a. The confluent-lane discharge (charter validation addition,
## RUN first-hand at the slice tip)

The slice-2 laws are proof-layer over the SAME
`applyChanOp`/`resumeThread`/`storeLoc`/delivery-frame code paths the
differential executes; the S1 §11 seven-id slice re-run first-hand at
the slice tip: **7/7 PASS**, the three goroutine rows at
`stage=confluent` with `|set|=1 certified over all schedules`
(`goroutines/fork-join/unbuffered` — the TARGETED unbuffered receive,
this slice's exemplar shape; `goroutines/fork-join/args-eval-now` —
the allocating spawn; `goroutines/rendezvous-hb/send-hb` — the
zero-target discard; the three close rows and
`builtins/make-channel-len-cap` strict). The exemplar program itself
remains a Lean-side seed, exercised by the fuel-500 kernel
certificate (schedule-exhaustive at the seed); zero corpus effect
stands.

**FD3 attestation (added at the S2 audit fix round — the S1
per-slice practice, dropped by the first form of this note):** nothing
is designated this slice; the 48 designated statements are
byte-identical (`git diff` over the branch range touches no designated
module). CANDIDATE RECORDED per FD3: **`spawnNoopSpecC`** — the
assembled `GoSpecC` the S4 note's §10 named as the decomposition
lane's designated-shape summit, now that P-S4-1 is paid; its F4
def-only-hoist cost is small (`spawnNoopCell`/`spawnNoopProg` already
live in proofs modules; a statement-module hoist like P-S3-1's).
`chanRendezvousValTripleC` is deliberately NOT a candidate: a
purpose-built exemplar, not a curated row — the designation-shaped
successors are the six rows' re-proofs (P-CL2-4).

**FD7 deviation, labeled (S2 audit fix round):** the DM simulation
lane carries `Classical.choice` where FD7's binding clause reads
"constructive [propext, Quot.sound] where the existing simulation
lane is". This is a RECORDED DEVIATION, not a silent one: root cause
re-measured at P-CL2-6 (the `BEq.rfl`/Ord route, not String/Int),
labeled at the Audit block, registrations accurate, LangD's lane
unchanged-constructive, fix parked as P-CL2-6.

Everything else this slice shipped — `StepDM`, the simulation, the
round-trip kit, `chanInvP`, the `wpDM_*` laws, the walks — is METHOD:
none of it appears in an exported statement (all statements above are
`execProg`/`loadLoc`/`GoTripleC`/`GoSpecC`/`TerminatesNormallyC`
vocabulary; Iris appears in no statement — the deletion test per
statement). The D1-BOTH convention is observed for the exemplar
(triple + completion pin, same commit); the completion-pin speedbump
covers the new `Specs.ChanRendezvousVal` module by its naming
convention.
