# The channel RESOURCE tier and the dsp flagship (channel-logic arc, slice 3)

Status: DESIGN OF RECORD for the slice, opened before building (the
binding discipline). Charter: `docs/2026-08-10_channel-logic-arc-charter.md`
work-plan item 3 on slice 2's measured prerequisites
(`docs/2026-08-11_channel-protocol-layer.md` §6: the dsp attempt blocks
on RESOURCE TRANSFER — pure-Ψp capability limit — plus the wpDM
sequential-law surface; P-CL2-3 with dsp its named flagship consumer;
P-CL2-4 the deferral this slice pays). Branch `channel-logic-s3` off
`channel-logic` @ 477a8871. FD1–FD9 apply. Everything in this slice is
proofs-side (FD6): no machine change, no new `Choices` site, no
envelope change, zero corpus effect.

## 1. The resource tier: `chanInv` with an `IProp`-valued per-element Ψ

Tier §3b(b)-first-form of the slice-2 note, now with its consumer. The
invariant is the `[∗list]` shape the S2 note originally sketched:

    chanInv (a : Addr) (cap : Nat) (Ψ : GoValue → IProp GF) : IProp GF :=
      ∃ buf : Array GoValue,
        ([∗list] v ∈ buf.toList, Ψ v)
          ∗ a.id ↦ (⟨none, .chanData buf cap false⟩ : HeapCell)

pinning exactly what `chanInvP` pins — the machine-real untyped cell
(`declaredTy = none`, what `makeChan` allocates: measured,
`applyStmtOpCore` `.makeChan` arm is `s.alloc (.chanData #[] capacity
false)`, the one-argument `alloc`), the OPEN shape (`closed = false`;
close-protocols remain the P-CL2-3 ghost tier), arbitrary capacity —
but each buffered element now CARRIES A RESOURCE `Ψ v`, not a pure
fact. What send and recv atomically exchange:

- **send/deposit** (arriving or parked): to complete, the sender
  re-establishes the invariant with the pushed buffer — it PAYS `Ψ v'`
  (a separation-logic resource, e.g. a points-to), which the big-op
  absorbs (`bigOpL` append/snoc). The send-side tie is carrier-fact:
  on `StepDM` a `.base` plain send has no phantom completion (S2 §2b
  rule 11), so every completion writes the value AND deposits the
  resource.
- **recv/drain** (arriving or parked): the receiver opens the
  invariant, observes `buf = v :: rest`, splits `Ψ v` off the big-op
  (`array_toList_head_erase`, the S2 hinge), re-establishes with
  `rest`, and the continuation RECEIVES `Ψ v`: ownership enters the
  receiving thread's walk with the message. This is the defining move
  of a session protocol and precisely what §6-obstacle-1 of the S2
  note proved the pure tier cannot do.

Law forms (`proofs/GoLeanProofs/ChanDMRes.lean`, prefix `wpDM_*_inv`):
`wpDM_send_inv`, `wpDM_blocked_send_inv`, `wpDM_recv_inv`,
`wpDM_blocked_recv_inv` — statement-for-statement the four `*_invP`
laws of `ChanDM.lean` with the pure obligation `Ψp v'` replaced by the
resource `Ψ v'` on the paying side, and the receive continuations
changed from `⌜… ∨ ∃ v, c' = deliverCfg v ∧ Ψp v⌝` to
`(⌜c' = park⌝ ∨ ∃ v, ⌜c' = deliverCfg v⌝ ∗ Ψ v)` — the delivered
disjunct is now a separating conjunction because it hands over a
resource. The parked-receive law stays the one `.MaybeStuck`-fixed
member (carrier irreducibility, S2 §2c — unchanged). House
obligations unchanged: FD7 axiom sets, same-commit witnesses, Audit
registration, docstrings scoped to the witness.

**The pure tier remains as the degenerate case.** `chanInvP` is
recovered by `Ψ v := ⌜Ψp v⌝` — `[∗list] v ∈ l, ⌜Ψp v⌝ ⊣⊢ ⌜∀ v ∈ l, Ψp
v⌝` (`bigOpL_pure`-shaped lemma, proved with the tier if cheap at the
pin, else recorded as a noted equivalence). The `*_invP` laws and
their exemplar are UNTOUCHED — no consumer migrates; the two tiers
coexist, the pure one as the cheaper interface for pure protocols
(every branch obligation a plain hypothesis, no big-op management).

**Scope: `.base` only, verified against the flagship.** The resource
tier inherits the mediated rules' `.base` scope (S2 §2a). dsp's
channels are machine-allocated — `makeChan` → `ExecState.alloc` →
`.base` cells — measured from the pinned lowering
(`Specs/ImportedGooseActris.lean`: both channels come from
`Stmt.makeChan`, no adversarial-seed path-loc anywhere in the row).
The non-`.base` ∃-residue (P-CL2-1) is untouched and still has no law
targeting it. The phantom-residue constraint from S2 §2 is therefore
inert for this slice: every cell any slice-3 law touches is `.base`.

**HoCAP/atomic-update forms: NOT taken this slice.** P-CL2-3's second
form (auth-ghost `own_chan` logical contents + au-style accessor laws
derived over the tier-1 laws) has no slice-3 consumer: dsp needs
ownership TRANSFER (the `[∗list]` tier), not logical-contents
tracking. Recording the option's status: it stays parked in P-CL2-3
for close-protocols/buffered-histories (with S2 §2c's closed-zero
forward warning), and nothing this slice builds obstructs deriving it
over `chanInv` later — the invariant's contents are exactly the
physical buffer, which is what an auth-ghost would mirror.

## 2. THE REPLY-LEG TIE — the phantom-name problem and the ghost tie
## taken (the slice's one genuinely new design point)

dsp's session (upstream `DSPExample`, Actris 2.0 prog3; our pinned
lowering): main allocates a cell `a` (`new(40)` — runtime address),
sends the boxed pointer on `c`; the child receives it, writes
`*ptr += 2`, and signals on `signal`; main receives the signal and
returns `*ptr` — 42. The points-to for `a` travels main → child on
`c`'s message and child → main on `signal`'s. The outbound leg is
tier-1: `Ψc v := ∃ a, ⌜v = box(ptr a)⌝ ∗ a.id ↦ ⟨40⟩ ∗ …`. The REPLY
leg is where a per-channel Ψ is structurally short: main must learn
that the cell coming back through `signal` is ITS `a` (its deref of
`ptr` needs `a.id ↦ ⟨42⟩` at that exact address), but

**the phantom-name problem:** both channels' protocols are fixed when
their invariants are created — BEFORE `a` exists (`makeChan` ×2 and
the fork precede `new(40)` in the body; the child needs both
`is_chan` assertions at spawn). So `Ψsignal` cannot mention `a`, and
`Ψsignal v := ∃ a', a'.id ↦ ⟨42⟩` alone delivers SOME written cell,
not main's. Upstream never meets this problem: Actris's dependent
protocol (`ref_prot` at `channel_dsp.v`, pin 43d4efa) binds `l`
ACROSS the two messages — `<! (l:loc) (x:Z)> MSG … {{ l ↦ x }} ; <?>
MSG … {{ l ↦ x+2 }}` — the iProto binder is the tie. We do not port
iProto (FD2: native; the Actris-lite port is the standing recorded
future option); we need a native tie.

Options at this latitude point:

- **(a) TAKEN — the gen_heap META tie.** The pin's gen_heap carries
  location METADATA: every `genHeap_alloc` yields `metaToken l ⊤`
  alongside the points-to (measured at the pin: `genHeap_alloc`'s
  conclusion), `meta_set : metaToken l E ==∗ metaInfo l N x` (↑N ⊆ E),
  `metaInfo` is PERSISTENT, and `meta_agree : metaInfo l N x₁ ∗
  metaInfo l N x₂ ⊢ ⌜x₁ = x₂⌝`. The tie: attach the late-chosen
  address as metadata ON AN ADDRESS BOTH PROTOCOLS ALREADY KNOW — the
  signal channel's own cell `sa`, whose address IS available when the
  invariants are created (it is `is_chan`'s parameter). Main's
  `makeChan signal` law hands out `metaToken sa ⊤` (the machine
  allocation's token, threaded through the law — §3); main holds it
  until `new(40)` produces `a`, then `meta_set` pins
  `metaInfo sa N a` (persistent — main keeps a copy);
  `Ψc v := ∃ a, ⌜v = box(ptr a)⌝ ∗ metaInfo sa N a ∗ a.id ↦ ⟨40⟩`
  carries the (duplicable) knowledge to the child with the pointer;
  `Ψsignal v := ∃ a, metaInfo sa N a ∗ a.id ↦ ⟨42⟩` carries it back;
  `meta_agree` at main's receive closes the loop: `a' = a`, the
  points-to is main's cell, the deref reads 42. Both Ψ's are
  `sa`-parametric — legal, `sa` is in scope at creation. Zero new
  ghost machinery, zero functor-bundle change, everything proven at
  the pin. Cost: a `Pos.Countable Addr` instance (the pin has
  Char/String/List/Pos only — a small local Nat/Addr instance,
  FD9-authorized local construction, recorded here).
- **(b) fallback, not taken — a ghost-map name allocated early, shot
  late.** Add a slot-7 functor to `GoCoreS` (`HeapView Nat (Agree
  (LeibnizO Addr)) GoHeapF`) + a `GhostMapG GoCoreS Nat Addr`
  instance; allocate `γ` empty before the invariants
  (`ghost_map_alloc_empty`), mention `γ` in both Ψ's,
  `ghost_map_insert_persist` 0 ↦ a after `new`, agree via
  `ghost_map_elem_agree`. Equivalent strength; rejected because it
  edits the concrete adequacy bundle (`Adequacy.lean`) that every
  proof in the repo elaborates against, for something (a) gets from
  machinery the bundle already carries. Kept as the fallback if (a)'s
  countability or reservation-map plumbing fights back (it did not).
- **(c) not taken — the `own_chan`/session tier.** Subsumes the tie
  (a logical session state ties the legs) at the cost of the full
  tier P-CL2-3 records; dsp does not need it, and building it
  flagship-first would be scaffold-shaped.

**What the invariant owns vs what transfers, stated for the flagship:**
each channel invariant owns its physical cell and the Ψ-resources of
the values CURRENTLY BUFFERED (at cap 0, transiently during the
deposit-drain decomposition); the points-to `a.id ↦ _` is owned by
main (birth → send), the channel invariant (send → recv, one machine
pairing decomposed as deposit-then-drain), the child (recv → signal
send), the signal invariant (transiently), then main again. The
`metaInfo` tie is persistent knowledge — owned by everyone who has
seen it, never returned. The handle cells (`c`/`signal` variable
cells, read by both threads after the fork — the child derefs its
`*chan` params into them) are PERSISTED read-only via
`pointsTo_persist` (`↦□`, available at the pin) — the same move as
upstream's `iPersist "c signal"` at the same program point; read laws
are stated at `↦{dq}` so both `↦` and `↦□` consumers use them.

## 3. The wpDM law-port inventory (S2 §6 obstacle 2, named ports)

The S1→S2 port pattern: same machine-equation content as the
sequential `Laws/*` family, restated on the DM carrier over the DM
cores, side-conditions `hsp/hsc/hblk/hpos` (all `rfl` at sequential
shapes — `stepDM_shape_cases` refutes the mediated rules away from
apply/blocked positions). New cores in `LangDM.lean` (internal
machinery, consumed by the ports, per the `Lifting.lean` precedent):

- `wpDM_alloc_step` — ONE fresh cell, continuation `∀ pa`-parametric
  (the `wp_init`/`enterFrame` allocation shape; `genHeap_alloc` +
  `HeapWf.fresh_get?`, the `wpDM_fork_alloc₁` interior). **Hands out
  the allocation's `metaToken pa ⊤`** — new to the DM kit, needed by
  §2(a); the sequential family discards it, ours must not.
- `wpDM_alloc_store_step` — fresh cell + a store into an owned cell
  (the `newValue`/`makeChan` shape: allocate the payload, store the
  handle/pointer into the target var's cell). Token handed out too.
- `wpDM_store_step₂` — the two-cell store (`wp_store_step₂`'s port:
  read `pa`, write `a` — the child's `*ptr = *ptr + 2`).
- `wpDM_fork_alloc₂` — the two-parameter spawn (`allocMany σ [p₁,
  p₂]`, child continuation over consecutive fresh addresses): dsp's
  `go lit0(&c, &signal)` shape, measured from the lowering.
- `wpDM_eval_var`/read laws generalized to `↦{dq}` (read-only needs
  `genHeap_valid`, which is dq-generic at the pin) — the persisted
  handle cells.

The named ports (`proofs/GoLeanProofs/LawsDM.lean`), each consumed by
the flagship walk and/or the §4 witnesses in the same commit:

| port | source pattern | dsp site |
|---|---|---|
| `wpDM_block_nil` | `wp_block_nil` | every body (`block #[] #[…]`) |
| `wpDM_init` | `wp_init` (alloc core) | 9 `initialization`s |
| `wpDM_make_chan` | NEW (P-CL1-6 closes; `applyStmtOpCore` `.makeChan` + alloc-store core; no sequential counterpart exists) | `make(chan any)` ×2 |
| `wpDM_new_value` | `wp_new_value` | `new(40)` |
| `wpDM_call_start` / `wpDM_call_enter_ret1` | `wp_call_start`/`wp_call_enter_ret1` | driver → `goleanDSPExample` → `DSPExample` (both nullary/1-int-result) |
| `wpDM_frame_return_int` | `wp_frame_return_int` | both frame exits |
| strict-spine ports (`wpDM_eval_strict`, `wpDM_strict_shift`, `wpDM_strict_apply_pure/pin/read`) | `Laws/Eval.lean` | `toInterface` (boxing, types-pinned), `typeAssert` (unboxing), `add`, `deref` (read at `↦{dq}`) |
| assign/tgtop-spine ports (`wpDM_assign_start`, `wpDM_tgtop_*`, `wpDM_rhs_*`, `wpDM_assign_store`, `wpDM_stores_done*`) | `Laws/Eval.lean` | `assign` ×5, `assignMany` (the phase-split `tgtOpK`/`rhsK`/`storeK` machinery — `assignMany` has no one-shot plan, BUG-025) |
| control ports (`wpDM_seqn`, `wpDM_seq_next`, `wpDM_seq_done`, `wpDM_frame_fall`, `wpDM_return`, `wpDM_eval_intLit`, `wpDM_eval_ref`) | `Laws/Control.lean`, `Laws/Eval.lean` | everywhere |

A port that turns conceptual (a rule shape fighting the DM carrier)
becomes a section here, not a silent hack — none did at build time
except where noted in §6's log.

## 4. Witnesses (non-vacuity, same-commit)

- **The resource tier's witness — `Specs/ChanTransfer.lean`
  (mini-dsp):** worker `(ch chan *int, p *int) { *p = 42; ch <- p }`,
  main `go worker(chv, &x); <-chv` over a pre-seeded rendezvous
  channel (the S1/S2 seed convention), pre `harness ∗ handle ∗
  chanCell ∗ x ↦ 40`, post `harness ∗ handle ∗ x ↦ 42`. The child
  owns `x`'s cell at its store (handed at fork), main re-acquires it
  ONLY through the message resource (`Ψ v := ⌜v = ptr x⌝ ∗ x.id ↦
  ⟨42⟩`) — the pure tier provably cannot state this post (S2 §6
  obstacle 1's shape, one leg). Discharges: all four resource laws +
  `wpDM_fork_alloc₂` + the store cores. D1-BOTH + completion pin per
  the convention.
- **The port witnesses:** the flagship walk itself is the named
  consumer for every port (§3's table, same commit as nothing — the
  ports land BEFORE the flagship). To keep the witness discipline
  same-commit, the port commit carries a compact single-threaded
  kitchen-sink witness (`Specs/SeqWalkDM.lean`-shaped: a driver
  calling a nullary/1-result function whose body runs `initialization`,
  `makeChan`, `newValue`, `toInterface`-boxing, `typeAssert`,
  `assignMany`, `returnStmt`) walked end-to-end on the DM carrier with
  a D1 readout — every port fires at least once, premises discharged
  at a concrete program.

## 5. The flagship route (P-CL2-4 pays)

`Specs/ChanDSP.lean`: the compositional re-proof of the dsp row over
the PINNED lowering (`actrisLowered` — the staleness-guarded frontend
term, not a hand transcription), at the row's established seed
convention (`dspDriver`/`dspEnv`/`dspSeed`,
`Specs/GooseParityTargets.lean`):

    GoTripleC actrisLowered.typeDefs.toList actrisLowered.funcs #[]
      dspEnv importedCell0-shaped-pre dspDriver (r ↦ ⟨int, 42⟩)

via laws → `wpDM` walk (both frames, the fork, the two protocol
channels under `chanInv` with §2(a)'s Ψ's, the meta tie) →
`goTripleC_of_wpDM`. D1-BOTH: the run-conditioned first-order readout
pinning `loadLoc σf r = 42` at the seed, + the completion pin — the
row ALREADY carries `dspTerminatesNormallyC` (designated-set-adjacent
kernel certificate family, `Specs/GooseParityChannels.lean` at fuel
400): the pair cites it rather than re-proving it; 42 is upstream's
`TestDSPExample` expected result and the differential row's pinned
verdict. The six rows' certificate families are untouched (they stay
validation; the triple becomes the headline for THIS row — charter
work-plan item 3's contract).

TCB-grounding walk (the per-slice criterion): the trusted endpoints
are (i) the run-conditioned `execProg`/`loadLoc` readout at the seed
pinning 42, and (ii) the pre-existing kernel completion certificate;
`chanInv`, the meta tie, `StepDM`, every law and the walk are
proof-side METHOD appearing in no exported statement (Iris deletion
test per statement; StepDM/StepDC are in the statement-TCB forbidden
set — S2 fix round — and all slice-3 exports stay
`execProg`/`loadLoc`/`GoTripleC`/`TerminatesNormallyC` vocabulary).

## 6. Build log (appended as built)

- **Commit 1** — this note.
- **Commit 2 — THE RESOURCE TIER + THE TRANSFER WITNESS**
  (`ChanDMRes.lean`, `Specs/ChanTransfer.lean`, `wpDM_fork_alloc₂` in
  `LangDM.lean`; Audit block + root imports). §1 built as designed:
  `chanInv` (the `[∗list]` IProp tier), the four `wpDM_*_inv` laws,
  `chanInv_pure_eqv` (P-CL3-1 DISCHARGED — `BigSepL.bigSepL_pure` was
  at the pin, so the degenerate case is a theorem, not prose), and the
  mini-dsp witness with D1-BOTH + completion pin (fuel 500,
  `#eval`-confirmed `true` before `decide +kernel`). In-build
  decisions, recorded:
  - **The timeless restriction** (`[∀ v, Timeless (Ψ v)]` on all four
    laws): invariant opening yields `▷ chanInv`, and the proofs strip
    the later by timelessness — free for the pure tier, a real
    restriction here. Covers every protocol this arc states
    (points-to/pure/`metaInfo` compositions are timeless at the pin);
    the later-credit generalization (needed only for genuinely
    higher-order Ψ, e.g. a nested WP) is parked as **P-CL3-3** with no
    current consumer.
  - **The park branch RETURNS the payment**: `wpDM_send_inv`'s
    continuation disjunction is `(⌜parked⌝ ∗ Ψ v') ∨ ⌜pushed⌝` — a
    resource, unlike the pure tier's freely-duplicable hypothesis, must
    round-trip through the park so the parked-send law can re-pay it.
    This is the one statement-shape delta from the `*_invP` family.
  - **`wpDM_store_step₂` was drafted and DELETED**: the machine's
    phase-split target resolution (the `tgtOpK`/`storeK` machinery)
    reads the pointer cell and writes the target cell in SEPARATE
    steps, so the two-cell store core has no consumer on the DM
    carrier (the sequential `wp_store_step₂` predates the split's
    reach here). Anti-scaffold rule applied; re-adding is one git
    revert away if a genuinely simultaneous two-cell step appears.
  Axiom sets FD7-exact (spec-lane classical trio; cert
  `[propext, Quot.sound]`; pure helpers `[propext]`); the DM lane's
  recorded `BEq.rfl`/Ord deviation (P-CL2-6) is inherited unchanged
  and cited at the Audit block. `scripts/ci` green at the commit.
- **Commit 3 — THE wpDM LAW PORTS + THE KITCHEN-SINK WITNESS**
  (`LawsDM.lean` ~46 laws, `Specs/SeqWalkDM.lean`; Audit block + root
  imports). §3's table built in full: the three cores
  (`wpDM_pure_step` over the generic `step_det`; the two allocating
  cores handing out `metaToken` — the §2(a) tie's raw material), the
  pure control/eval/go/chan glue, the strict spine (`toInterface`/
  `typeAssert` at the types pin, the deref read at `↦{dq}`), the
  assign/`assignMany` spine, **`wpDM_make_chan` (P-CL1-6 CLOSES)**,
  `wpDM_new_value`, `wpDM_init`, `wpDM_call_enter_ret1`,
  `wpDM_frame_return_int`; `wpDM_eval_var` generalized to `↦{dq}` in
  place (safe: existing call sites unify at `.own 1`). In-build
  decisions, recorded:
  - **The DM laws are `@[go_walk_law]`-registered.** The
    `wp_init_bool` precedent warns that the table is a global tactic
    surface; the DM entries are safe by DISCRIMINATION — their
    conclusions are `WP (PoolCfgDM.mk _)`, a different head than the
    sequential `WP (_ : Config)` keys, so neither family can fire on
    the other's goals. Validated empirically: the same `scripts/ci`
    run rebuilds every standing sequential walk green. `go_walk`
    DRIVES DM WALKS — the kitchen-sink witness's pure glue is
    `go_walk` end to end, a large cost reduction for the flagship.
  - No port turned conceptual: every rule shape carried over
    mechanically (the §3 escape clause was not needed).
  Witness: the kitchen-sink program (make-chan → new → boxing →
  unboxing → multi-assign → deref/add → both frames, verdict 42),
  `seqWalkTripleC` + readout + fuel-500 completion pin
  (`#eval`-confirmed first). Axiom sets FD7-exact. `scripts/ci` green
  at the commit.
- **Commit 4 — THE FLAGSHIP: dsp PROVED** (`Specs/ChanDSP.lean`;
  Audit block + root import; **P-CL2-4 PAYS in full — no deferral**).
  `dspCompTripleC`: the dsp row as a compositional frame-quantified
  `GoTripleC` over the PINNED lowering at the row's established seed
  convention — every `.normal` completion leaves the harness cell at
  **42**, proved laws → wpDM → resource tier → meta tie → exit,
  never by execution. §5's route held exactly; in-build findings:
  - **The meta tie worked as designed** (§2(a)): `Pos.Countable`
    Nat/Addr local instances (the FD9-recorded construction),
    `metaInfo` Timeless/Persistent by instance inference at the pin,
    `meta_set` on the signal `makeChan`'s token after `new(40)`,
    `meta_agree` closing `x' = x` at main's receive. Zero
    functor-bundle changes — option (b) never needed.
  - **Pinned-lowering fidelity is `rfl`-anchored**: the three
    transcribed bodies (`dspChildBody_eq`/`dspMainFn_eq`/
    `dspGoleanFn_eq`, axiom-FREE equations against `actrisLowered`) —
    a transcription or frontend drift fails the build in the same run
    that trips `check-imported-pins`. One real transcription error
    (the fork's ref args sit in the `funcVal`'s CAPTURED list, not
    the `goStmt` args) was caught by exactly this anchor.
  - **One value-kind correction caught by the walk**: dsp's `new(40)`
    is `intLit 40 (.int)` — the transferred cell holds `.int 40 .int`
    (the S2-style exemplars use the default unbounded kind); `dspΨC`
    pins the machine-real kind.
  - **A go_walk table finding**: `wpDM_strict_apply_read` was
    UNREGISTERED from the table — its `happly` discharges by `rfl` at
    any PURE strict apply while the owned cell stays
    meta-undetermined, so `iframe` grabs an arbitrary points-to (a
    spurious resource capture, observed renaming a live hypothesis).
    Genuine reads supply the law explicitly; docstring records the
    hazard. (The sequential twin's registration is left untouched —
    out of this slice's concern; flagged for the audit.)
  - Walk structure: three private tail lemmas (`dsp_child_after_recv`,
    `dsp_main_after_send`, `dsp_main_final`) shared across the
    park/immediate branches at each rendezvous — the branch tails are
    proved ONCE.
  D1-BOTH: `dspCompReadoutC` (run-conditioned first-order 42 readout
  at `dspSeed`) + `dspCompTerminatesNormallyC` (the row's STANDING
  fuel-400 kernel pin, restated beside the triple per the
  completion-pin convention; certificate not re-proved). Axiom sets
  FD7-exact (triple/readout/witness the classical trio; norm helpers
  `[propext]`; transcription anchors axiom-free). `scripts/ci` green
  at the commit.

## 7. Perennial comparison (shape reference, deltas both directions)

Upstream's dsp proof (`channel_dsp.v` @ 43d4efa, `wp_DSPExample`,
Qed): Actris-style `iProto` (`ref_prot`), the `dsp` idiom pairing the
two raw channels into one session endpoint (`dsp_session_init`), `↣`
endpoint ownership, `wp_send/wp_recv` proofmode. Deltas, recorded and
deliberate:

- THEIRS: the location binder is shared across the protocol's two
  messages (dependent protocols — the tie is iProto's binder
  structure). OURS: two per-channel `chanInv` protocols + the
  persistent gen_heap meta tie (§2a) — strictly less machinery, no
  protocol calculus, at the cost of a per-session ghost-tying idiom
  rather than a reusable session-type combinator language. The
  combinator language remains the recorded future option (FD2, P-CL2-3).
- THEIRS: `iPersist "c signal"` persists the handle heap cells. OURS:
  identical move (`pointsTo_persist`, `↦{dq}` read laws) — recorded as
  convergence, adopted from reading their proof.
- THEIRS: session init consumes both channels' `own_chan` at creation.
  OURS: `inv_alloc` per channel at the walk's makeChan sites.
- OURS ONLY: the executable grounding — the triple is run-conditioned
  over `execProg` with the differential-validated interpreter and the
  row's kernel completion certificate; their WP is over a Rocq model
  no test executes. THEIRS ONLY: `NotStuck` (deadlock-freedom-shaped
  safety) — ours is `.MaybeStuck` by carrier design (S2 §2c), with
  deadlock classes covered separately by the row's certificate family
  (`dspNoDeadlock`, kernel-checked, all schedules at the seed).

## 8. Parking ledger (slice 3)

- **P-CL3-1 — `bigOpL` pure-collapse lemma: DISCHARGED at commit 2**
  (`BigSepL.bigSepL_pure` was at the pin; `chanInv_pure_eqv` is a
  theorem).
- **P-CL3-2 — loop-invariant machinery for the muxer `client` row**:
  measured design recorded at §9 (the successor entry).
- **P-CL3-3 — later-credit generalization of the resource laws**: the
  four `wpDM_*_inv` laws carry `[∀ v, Timeless (Ψ v)]` (commit-2 log);
  points-to/pure/`metaInfo` protocols — everything this arc states —
  are timeless. Needed only for genuinely higher-order Ψ (a nested
  WP/saved-prop payload); no consumer, reversible (restate with
  `£`-elimination at the invariant opening).
- **P-CL3-4 — capacity-carrying `wpDM_make_chan`**: the landed law is
  the `hasCap = false` form (dsp's shape). `async` needs
  `make(chan string, 1)` (measured, §9) — a mechanical variant over
  the same `applyStmtOpCore` arm with the capacity operand; the
  protocol laws are already cap-generic. Lands with the async row.
- **P-CL3-5 — the sequential `wp_strict_apply_read` registration**:
  the DM twin was unregistered from the `go_walk` table after the
  spurious-iframe-capture finding (commit-4 log); the SEQUENTIAL
  twin's `@[go_walk_law]` registration has the same latent hazard but
  was left untouched (out of this slice's tree-of-concern; standing
  sequential walks are green, so any capture there is currently
  benign). Flagged for the audit / a maintenance pass.

## 9. Reach check (measured at the landed surface, per the charter
## item — first-hand statement inventories of `muxerLowered`)

Per-function counts (`while`/`select`/chan-ops), measured from the
pinned lowering at this slice's tip:

- `Async` {goStmt 1, makeChan 1(+cap)}, `Async$lit0` {chanSend 1},
  `goleanAsync` {chanRecv 1, call 1} — **zero `while`, zero
  `select`**.
- `Client` {chanSend 1, chanRecv 1, call 1}, its server `Serve`
  {goStmt 1, makeChan 2} and `Serve$lit0` **{while 1, chanRecv 1,
  chanSend 1, if 2, break 1}** — the one live loop; zero `select`.

**async: REACHABLE with the landed surface plus exactly one small law
variant** — the capacity-carrying `makeChan` (P-CL3-4). Everything
else in its walk (fork with captured ref args, buffered send/recv —
the protocol laws are cap-generic since S2 — call frames, string
payload) is landed. No loop-invariant machinery needed.

**client: blocked on ONE thing — loop-invariant machinery for the
spawned server, and the loop is NOT unrollable.** `Serve$lit0`'s
`for { s.res <- f(<-s.req) }` is an unbounded service loop: after
serving a request it re-parks at the receive (the certificate row
leaves it parked at main's exit), so no finite unrolling covers the
child's WP. The successor design, recorded (P-CL3-2): a DM port of
the loop rule in `wp_while_inv`'s shape with the iteration proved by
LÖB — each iteration passes through the step laws' `▷`, so the
guarded fixpoint closes — carrying the two `is_chan` assertions (and
the break-on-closed branch, which is where S2 §2c's closed-zero
forward warning becomes live: the server's exit path receives the
closed-channel default, so the loop invariant meets the
close-protocol tier, P-CL2-3's remaining half). The row's
request/response protocols themselves fit the landed resource tier
as-is. The select trio remains the ONLY select consumer (measured
zero selects in the async/client call graphs) — P-CL1-2 unchanged.

## 10. The TCB-grounding walk (the per-slice review criterion)

| exported artifact | (i) trusted endpoint (interpreter vocabulary) | (iii) executable anchor |
|---|---|---|
| `dspCompTripleC` | ∀ admissible seeded heap, run-conditioned: `execProg … dspDriver = .ok (.normal σf, _)` → `loadLoc σf r = .ok (.int 42 .int)` | run-conditioned only — anchored by the pin row below (the standing `ChanVacuityWarning` demonstration) |
| `dspCompReadoutC` | the same, first-order at `dspSeed` — **the 42 pin in `loadLoc` vocabulary** | premises discharged at the seed (kernel `decide` for the split); consumes the triple as method |
| `dspCompTerminatesNormallyC` | ∃N ∀fuel≥N ∀ch: `.normal` completion | the row's STANDING fuel-400 kernel certificate (`dspCert400`, `#eval`-first per its record) — restated, not re-proved |
| `chanTransferTripleC` / `ReadoutC` / `TerminatesNormallyC` | as the commit-2 log: run-conditioned `x = 42` re-owned through the message; first-order at the seed; fuel-500 kernel pin | `chanTransferAllStreamsCert` (`#eval`-confirmed first) |
| `seqWalkTripleC` / `ReadoutC` / `TerminatesNormallyC` | run-conditioned `r = 42` through make-chan/new/boxing/unboxing/multi-assign/frames; first-order at the seed; fuel-500 kernel pin | `seqWalkAllStreamsCert` (`#eval`-confirmed first) |

Everything else this slice shipped — `chanInv`, the four resource
laws, the meta tie, the `Pos.Countable` instances, LawsDM's ~46
ports, the three private dsp tail lemmas, the walks — is METHOD: none
appears in an exported statement (all statements above are
`execProg`/`loadLoc`/`GoTripleC`/`TerminatesNormallyC` vocabulary;
Iris appears in no statement; `StepDM`/`StepDC` are in the
statement-TCB forbidden set and appear in no export — the deletion
test per statement). The FD7 `BEq.rfl`/Ord classical deviation
(P-CL2-6) is inherited by the DM lane unchanged and cited at each
Audit block, not re-investigated.

**FD3 attestation (the per-slice practice):** nothing is designated
this slice; the 48 designated statements are byte-identical (the
branch touches no designated module; the ci statement-TCB closure and
byte-set gates are green at every commit). CANDIDATES RECORDED per
FD3, for the arc-end designation window:

- **`dspCompTripleC` + `dspCompReadoutC`** — THE expected flagship
  pair (charter FD3's "the dsp pair's successor triples are the
  expected flagships"): the first six-row re-proof, over the pinned
  lowering, at the row's designated-certificate seed. F4
  def-only-hoist cost: `importedCell0`/`importedCellV`/`dspDriver`/
  `dspEnv`/`dspSeed` already live in the def-only
  `GooseParityTargets`; the statement additionally references
  `GoTripleC` (Surface, already in the trusted closure) — the hoist
  is near-zero. `dspCompTerminatesNormallyC` completes the D1 pair
  (its underlying `dspCert`/`dspAllSchedules` are ALREADY
  designated, D3 2026-08-10).
- `chanTransferTripleC` is deliberately NOT a candidate (purpose-built
  exemplar, the `chanRendezvousValTripleC` precedent); `seqWalkTripleC`
  likewise (a witness program, not a curated row).
