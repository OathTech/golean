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

**Standing docstring element for DELIVERY laws (adopted at the S3 fix
round; the S2 lesson's third occurrence).** Every send/receive law's
docstring must state the `closed = false` SCOPING explicitly: the
outcome sets these laws describe (drain-with-`Ψ`, park, no
closed-panic) hold only because `chanInv`/`chanInvP` pin the OPEN cell
shape. On a closed empty channel the machine resumes a parked receiver
with the type's ZERO value and `ok = false` (`Multi.lean` `.blockedRecv`
arm) — delivering no message and no `Ψ`. The send law already carried
its clause ("the closed-panic branch is refuted by the invariant's open
shape"); the two receive laws did not, and now do. This is a docstring
rule, not a statement change: the scoping is real in the statements
(the invariant is a hypothesis), it was simply unstated where a reader
would look for it. Any future close-protocol tier (P-CL2-3) restates
these outcomes at a `closed`-generic invariant.

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
  the pin. Cost: **exactly one `Pos.Countable Addr` instance** (the
  pin has Char/String/List/Pos only — a small local construction,
  FD9-authorized, recorded here). `metaToken`/`metaInfo` constrain
  only the METADATA type, never the location index, so the metadata
  being `Addr` is the whole requirement. (Corrected at the S3 fix
  round: this line and the commit-4 log said "Nat/Addr". A dead
  `Pos.Countable Nat` instance did ship at `Specs/ChanDSP.lean` — used
  by zero declarations, measured, and an unscoped global instance on a
  ubiquitous type — and was DELETED at the fix round. Only the `Addr`
  instance is the tie's construction.)
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
apply/blocked positions). New cores (internal machinery, consumed by
the ports, per the `Lifting.lean` precedent). **File attribution
corrected at the S3 fix round** — this list originally said "new cores
in `LangDM.lean`" for all of them, which is wrong for the two
allocating cores; measured locations are given per bullet:

- `wpDM_alloc_step` (**`LawsDM.lean`:68**) — ONE fresh cell,
  continuation `∀ pa`-parametric (the `wp_init`/`enterFrame`
  allocation shape; `genHeap_alloc` + `HeapWf.fresh_get?`, the
  `wpDM_fork_alloc₁` interior). **Hands out the allocation's
  `metaToken pa ⊤`** — new to the DM kit, needed by §2(a); the
  sequential family discards it, ours must not. (The kit rule has one
  recorded EXCEPTION, `wpDM_fork_alloc₂` — see below.)
- `wpDM_alloc_store_step` (**`LawsDM.lean`:131**) — fresh cell + a
  store into an owned cell (the `newValue`/`makeChan` shape: allocate
  the payload, store the handle/pointer into the target var's cell).
  Token handed out too. (`wpDM_pure_step`, the third core, is at
  `LawsDM.lean`:52.)
- ~~`wpDM_store_step₂` — the two-cell store (`wp_store_step₂`'s port:
  read `pa`, write `a` — the child's `*ptr = *ptr + 2`).~~ **DRAFTED
  AND DELETED at commit 2** (anti-scaffold; the machine's phase-split
  target resolution leaves it consumer-less — §6's log). Struck here
  so the plan table does not read as shipped surface.
- `wpDM_fork_alloc₂` (**`LangDM.lean`:2380**) — the two-parameter
  spawn (`allocMany σ [p₁, p₂]`, child continuation over consecutive
  fresh addresses): dsp's `go lit0(&c, &signal)` shape, measured from
  the lowering. **Recorded deviation from the token rule above (S3 fix
  round, audit note):** it binds both fresh cells' `metaToken`s in its
  proof and DISCARDS them — the child receives the two points-tos
  only, so a forked parameter cell cannot carry a meta tie. Not a
  soundness issue (dropping a resource only weakens the law) and no
  consumer needs it today; the deviation is now stated at the law's
  docstring. Threading them is a statement change to a landed law plus
  its witness, so it was NOT taken inside a records fix round —
  reversible whenever a consumer appears (the proof already binds
  `Htok₁`/`Htok₂`).
- `wpDM_eval_var` (**`LangDM.lean`:2203**)/read laws generalized to
  `↦{dq}` (read-only needs `genHeap_valid`, which is dq-generic at the
  pin) — the persisted handle cells.

The named ports (`proofs/GoLeanProofs/LawsDM.lean`), each consumed by
the flagship walk and/or the §4 witnesses in the same commit:

| port | source pattern | dsp site |
|---|---|---|
| `wpDM_block_nil` | `wp_block_nil` | every body (`block #[] #[…]`) |
| `wpDM_init` | `wp_init` (alloc core) | 9 `initialization`s |
| `wpDM_make_chan` | NEW (P-CL1-6 closes; `applyStmtOpCore` `.makeChan` + alloc-store core; no sequential counterpart exists) | `make(chan any)` ×2 |
| `wpDM_new_value` | `wp_new_value` | `new(40)` |
| `wpDM_call_enter_ret1` | `wp_call_enter_ret1` | driver → `goleanDSPExample` → `DSPExample` (both nullary/1-int-result) |
| `wpDM_frame_return_int` | `wp_frame_return_int` | both frame exits |
| strict-spine ports (`wpDM_eval_strict`, `wpDM_strict_shift`, `wpDM_strict_apply_pure/pin/read`) | `Laws/Eval.lean` | `toInterface` (boxing, types-pinned), `typeAssert` (unboxing), `add`, `deref` (read at `↦{dq}`) |
| assign/tgtop-spine ports (`wpDM_assign_start`, `wpDM_tgtop_*`, `wpDM_rhs_*`, `wpDM_assign_store`, `wpDM_stores_done*`) | `Laws/Eval.lean` | `assign` ×5, `assignMany` (the phase-split `tgtOpK`/`rhsK`/`storeK` machinery — `assignMany` has no one-shot plan, BUG-025) |
| control ports (`wpDM_seqn`, `wpDM_seq_next`, `wpDM_seq_done`, `wpDM_frame_fall`, `wpDM_return`, `wpDM_eval_intLit`, `wpDM_eval_boolLit`, `wpDM_eval_ref`) | `Laws/Control.lean`, `Laws/Eval.lean` | everywhere (`wpDM_eval_boolLit` has NO dsp site — see below) |

A port that turns conceptual (a rule shape fighting the DM carrier)
becomes a section here, not a silent hack — none did at build time
except where noted in §6's log.

**Two corrections to this table, made at the S3 fix round (audit
findings, both records-only):**

- The planned row `wpDM_call_start` / `wpDM_call_enter_ret1` was
  shipped as `wpDM_call_enter_ret1` ALONE: no `wpDM_call_start` exists
  anywhere in the tree, because the nullary `.call targets fid #[]`
  shape is consumed by the entry law directly and needs no separate
  start step. The port was dropped as unnecessary and the drop was
  never recorded — §6's "table built in full" is corrected there.
- `wpDM_eval_boolLit` was built but is NOT in this plan table (an
  unlisted extra) and has no dsp site: the three slice-3 programs
  contain no boolean literal. Its discharge witness is
  `wpDM_eval_boolLit_witness` in `Specs/SeqWalkDM.lean`, added at the
  fix round (§11) — the future consumers are the muxer rows, whose
  loop guards and `if`s are `Expr.boolLit` (measured, §9).

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
  imports). §3's table built, with ONE planned row dropped and one
  extra added (this sentence originally read "§3's table built in
  full", which was inaccurate — corrected at the S3 fix round;
  `wpDM_call_start` was dropped as unnecessary at the nullary call
  shape and `wpDM_eval_boolLit` was built without being listed, both
  now recorded at §3): the three cores
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
    the other's goals. **Evidence, restated honestly at the S3 fix
    round** (this line originally read "Validated empirically: the
    same `scripts/ci` run rebuilds every standing sequential walk
    green", which cannot support the claim and is withdrawn — the
    audit measured the `go_walk` table directly at a standing
    sequential walk: 51 entries, 0 of them DM, because the law table
    is a scoped env extension and NO standing sequential-walk module
    has `LawsDM` in its import closure; those walks were replayed from
    cache, not re-elaborated):
    - the DISCRIMINATION argument is STRUCTURAL, not empirical — the
      `PoolCfgDM.mk` wrapper is a distinct `DiscrTree` head, so the
      two families' keys cannot collide;
    - what the standing sequential walks DO show is NO REGRESSION
      (nothing this slice added perturbed them), which is worth having
      and is a different claim from disjointness;
    - the direction that IS exercised in-build is the converse:
      `SeqWalkDM`/`ChanDSP` run ~60 `go_walk` calls on DM goals with
      all 51 sequential entries in scope, and no sequential entry
      fires on them;
    - the untested direction (DM entries in scope at a sequential
      goal) arises nowhere in the repo today, since only the root
      aggregator, `SeqWalkDM` and `ChanDSP` import `LawsDM`. The audit
      ran the missing probe by hand (a verbatim copy of a standing
      sequential walk plus `import GoLeanProofs.LawsDM`: 32 DM entries
      in the table, elaborates clean at the same cost); a permanent
      cross-family probe module is the honest way to make this
      empirical and is left as a maintenance item beside P-CL3-5.
    `go_walk` DRIVES DM WALKS — the kitchen-sink witness's pure glue is
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
  - **The meta tie worked as designed** (§2(a)): the local
    `Pos.Countable Addr` instance (the FD9-recorded construction — a
    `Pos.Countable Nat` instance shipped beside it and was dead, since
    deleted, S3 fix round),
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
- **P-CL3-6 — the async/client PORT INVENTORY** (opened at the S3 fix
  round, from §9's corrected walk-level check). Three DM ports the
  async and client rows both need and that no landed law covers:
  1. **arg-carrying call entry** — the 1-arg/1-result shape
     (`goleanAsync → Async`, `Client → Serve`); landed
     `wpDM_call_enter_ret1` is nullary-only. Sequential shapes:
     `wp_call_enter_arg1` (1-arg/0-result), `wp_call_enter₂₁`
     (2-arg/1-result). Mechanical-leaning.
  2. **`Stmt.callValue`** — indirect call through a deref'd func
     pointer (`Async$lit0`, `Serve$lit0`); NO DM law exists.
     Sequential spine: `wp_call_value_start` +
     `wp_call_value_enter_cap1` (`Laws/Unwind.lean`:64, :324). NEEDS
     DESIGN: the callee is an expression evaluated into
     `callValCalleeK` first, so the port sits a continuation against
     the mediated apply/blocked side-conditions rather than restating
     one step.
  3. **non-int frame exit** — `chan string`/`string`/`Ty.defined
     main.stream` results; landed `wpDM_frame_return_int` is int-only.
     Sequential twins `wp_frame_return₁`/`₂` are general.
     Mechanical-leaning.
  Named consumer: the async and client row attempts in the successor
  slice — these land WITH the rows, not speculatively (anti-scaffold),
  and the capacity-carrying `makeChan` (P-CL3-4) rides along with
  async. NOT a complete list by construction: it is what a statement-
  by-statement read of the two call graphs found, and the walk itself
  may surface more (candidates not yet checked: `funcVal`-as-argument
  parameter binding, `Serve$lit0`'s `main.stream` struct-pointer
  params). The honest form of the reach claim is "at least these".
- **P-CL3-5 — the sequential `wp_strict_apply_read` registration**:
  the DM twin was unregistered from the `go_walk` table after the
  spurious-iframe-capture finding (commit-4 log); the SEQUENTIAL
  twin's `@[go_walk_law]` registration has the same latent hazard but
  was left untouched (out of this slice's tree-of-concern; standing
  sequential walks are green, so any capture there is currently
  benign). Flagged for the audit / a maintenance pass.

## 9. Reach check (measured at the landed surface, per the charter
## item — first-hand statement inventories of `muxerLowered`)

**REWRITTEN AT THE S3 FIX ROUND (2026-08-11).** The first form of this
section reported "async: REACHABLE … plus exactly one small law
variant" and "client: blocked on ONE thing". Both conclusions were
WRONG, and the way they were wrong is the section's most useful
lesson, so it is stated before the corrected accounting:

> **The measurement-scope lesson.** What was measured was a
> per-function inventory of `while`/`select`/chan-ops. That inventory
> is accurate — the audit reproduced every count. What was WRITTEN was
> a conclusion about the whole walk ("everything else in its walk … is
> landed"), which quantifies over dimensions the inventory never
> counted: CALL SHAPE (arity of the callee's `args`), CALL FORM
> (`Stmt.call` vs `Stmt.callValue`), and RESULT TYPE (the landed exit
> law is int-only). Counting three node kinds and concluding about all
> of them is the error. A reach check is a claim about a WALK, so its
> unit of measurement must be the walk: for each statement of each
> function in the call graph, name the landed law whose conclusion
> matches, or name the missing port. Below, what WAS measured is
> separated from what the walk-level check found.

**(a) What was measured — per-function counts (`while`/`select`/
chan-ops) from the pinned lowering at this slice's tip.** Accurate as
recorded; independently reproduced at the fix round:

- `Async` {goStmt 1, makeChan 1 with capacity `some (intLit 1 .int)`},
  `Async$lit0` {chanSend 1}, `goleanAsync` {chanRecv 1, call 1} —
  **zero `while`, zero `select`**.
- `Client` {chanSend 1, chanRecv 1, call 1}, its server `Serve`
  {goStmt 1, makeChan 2, both capacity `none`} and `Serve$lit0`
  **{while 1, chanRecv 1, chanSend 1, if 2, break 1}** — the one live
  loop; zero `select`.
- Zero `select` and zero `close` in the ENTIRE `muxerLowered` unit
  (case-insensitive grep = 0). The select trio therefore remains the
  ONLY select consumer — P-CL1-2 unchanged.

**(b) What the walk-level check found — three UNMADE DM ports, in
addition to the parked `makeChan` variant.** Each is a shape whose
node appears in the row's call graph and whose conclusion no landed
`wpDM_*` law matches (full DM inventory: 60-odd `wpDM_*` theorems
across `LangDM`/`ChanDM`/`ChanDMRes`/`LawsDM`; the sequential family
is NOT a fallback — the carriers are disjoint by construction, §6's
discrimination note):

1. **Arg-carrying call entry.** `goleanAsync` does
   `Stmt.call #[$c17] {Async} #[Expr.funcVal {goleanAsync$lit0} #[]]`
   and `Async.args = #[{f : funcType [] [string]}]`; `Client` calls
   `Serve` with a `funcVal` argument the same way. The only landed DM
   entry law, `wpDM_call_enter_ret1`, carries `hargs : func.args = #[]`
   and concludes over `.call targets fid #[]` — nullary only (§3's own
   table said so; §9's first form did not read it).
2. **`Stmt.callValue` (indirect call through a deref'd func pointer).**
   `Async$lit0`'s body is
   `Stmt.callValue #[$c3] (Expr.deref (Expr.var "f$cap") …) #[]`;
   `Serve$lit0` has the same shape with a string argument. There is NO
   `callValue` law on the DM carrier at all (`grep -c callValue` over
   the DM files = 0).
3. **Non-int frame exit.** `Async.results = #[chan both string]`,
   `goleanAsync.results = #[string]`, `Serve.results =
   #[Ty.defined main.stream]`. The only landed value-exit law,
   `wpDM_frame_return_int`, is int-fixed on both cells
   (`⟨some (.int kind), .int m kind⟩`, `IntKind.normalize`).
   (`wpDM_frame_fall` does cover `Async$lit0`'s void exit.)

Sequential twins, measured, since they set the cost: (1) has
`wp_call_enter_arg1` (1-arg/0-result) and `wp_call_enter₂₁`
(2-arg/1-result) — the SHAPE exists but not the 1-arg/1-result
instance the rows need; (3) has the general `wp_frame_return₁`/`₂`;
(2) has a two-law spine, `wp_call_value_start` +
`wp_call_value_enter_cap1` (`Laws/Unwind.lean`:64, :324). So (1) and
(3) are restatement-shaped (mechanical-leaning, the S1→S2 port
pattern), while (2) is the one needing DESIGN attention on the DM
carrier: its callee is an EXPRESSION evaluated first, so the port must
sit the `callValCalleeK` continuation against the mediated rules'
apply/blocked side-conditions rather than restate a single step.

**async: NOT reachable with the landed surface.** It needs the
capacity-carrying `makeChan` (P-CL3-4, a mechanical variant) PLUS
ports (1), (2) and (3) above. What IS landed for it, and was correctly
identified: the fork with captured ref args (`wpDM_fork_alloc₂`), the
buffered send/recv (the protocol laws are cap-generic since S2), the
string payload, no loop machinery. The port inventory is parked as
**P-CL3-6** (§8) with the async/client row attempts as its named
consumer.

**client: blocked on the loop machinery AND the same three ports.**
The loop diagnosis stands and re-measures correct: `Serve$lit0`'s
`for { s.res <- f(<-s.req) }` is an unbounded service loop — after
serving a request it re-parks at the receive (the certificate row
leaves it parked at main's exit), so no finite unrolling covers the
child's WP. The successor design, recorded (P-CL3-2): a DM port of the
loop rule in `wp_while_inv`'s shape with the iteration proved by LÖB —
each iteration passes through the step laws' `▷`, so the guarded
fixpoint closes — carrying the two `is_chan` assertions. The row's
request/response protocols themselves fit the landed resource tier
as-is.

**The break-on-closed attachment was a MISATTRIBUTION — withdrawn.**
The first form of this section said the client row's loop rule must
carry "the break-on-closed branch … so the loop invariant meets the
close-protocol tier, P-CL2-3's remaining half". Measured, `Serve$lit0`
has no such branch and no reachable exit at all:

- its guard is `Expr.boolLit true`, and its ONLY `break` is the
  else-branch of a second literal-`true` test — the standard `for {}`
  lowering, structurally dead (this is the `break 1` the inventory
  above counts);
- its receive is `chanRecv #[$c8] …` — ONE assignee, no `ok` flag, so
  closedness is not even observable there;
- nothing anywhere in `muxerLowered` closes a channel (`close` count
  = 0), and the Go source agrees (`Corpus/coverage/exec/imported-goose/
  channel/muxer/main.go`, byte-identical to goose's `muxer.go`).

The break-on-closed shape the withdrawn clause described is real but
belongs to a DIFFERENT function: `Muxer`, which does
`chanRecv #[$rrecv, $rok]` then `if not $rok then break` — and `Muxer`
is NOT in the client row's call graph (`clientDriver → goleanClient →
Client → Serve → Serve$lit0`; `Muxer` is reached only from
`makeGreeting`). So the client row does NOT meet the close-protocol
tier, and P-CL2-3's remaining half is NOT on its critical path.

The correction has a real design consequence, which is why it matters
more than a scoping slip: because `Serve$lit0` has no reachable exit,
the successor loop rule for this row cannot be `wp_while_inv`'s
ordinary "post on exit" shape — it is the NEVER-EXITING instance (Löb
with an unreachable post; the child's WP is `True`-posted at the fork,
which is what `wpDM_fork_alloc₂` already hands it). S2 §2c's
closed-zero forward warning stays correctly scoped where S2 put it (at
close-protocols generally); it becomes live at whichever row first
runs `Muxer`, not here.

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
  is near-zero. `dspCompTerminatesNormallyC` completes the D1 pair —
  **provenance corrected at the S3 fix round**: it is a direct
  restatement of `ChannelActris.dspTerminatesNormallyC`, which is
  `chanCert_terminatesNormallyC dspCert400`, i.e. it rests on the
  FUEL-BASED `dspCert400`, which D3 (2026-08-10) deliberately left
  UNDESIGNATED. The already-designated `dspCert`/`dspAllSchedules` are
  NOT what this member depends on (the earlier text said they were).
  The restatement itself is honest and delta-free (same proposition,
  same env/seed/program, discharged by direct reference); what changes
  is the designation calculus: designating the completion member at
  the arc-end window means either pulling `dspCert400` into the
  designated set or accepting a designated statement whose proof leans
  on undesignated kernel evidence. That decision is the user's at the
  window, and it should be made against the TRUE dependency.
- `chanTransferTripleC` is deliberately NOT a candidate (purpose-built
  exemplar, the `chanRendezvousValTripleC` precedent); `seqWalkTripleC`
  likewise (a witness program, not a curated row).

Candidates now ALSO accumulate in one place per FD3: the charter's
"FD3 candidate ledger" section (added at the S3 fix round — before it,
each slice's candidates lived only in that slice's own note, so the
arc-end window would have had to gather them by reading every note).

## 11. The S3 audit fix round (2026-08-11)

Pre-merge sub-branch audit of the slice-3 tip (306ca14c): 11 agents,
reviewers and verifiers Opus-class, every finding independently
reproduced from primary sources before being accepted. **The flagship
and the resource tier survived untouched** — no theorem statement, no
proof, no axiom set, no gate, and no designated statement is affected
by anything below. Two majors and the rest were RECORD defects: the
slice's central charter deliverable (§9's reach check) drew wrong
conclusions from a correct measurement. Dispositions, finding by
finding:

**Majors (both are the same defect, filed twice by decorrelated
reviewers) — §9's reach-check overclaim, for BOTH rows.**

- FIXED BY HONEST RECORD, not by landing ports: §9 is rewritten above
  with the measurement-scope lesson stated first, the measured
  inventory separated from the walk-level check, and the three unmade
  DM ports named per row. The ports themselves belong to the successor
  slice that consumes them (they land WITH the async/client rows —
  landing them here would be scaffold), and are parked as **P-CL3-6**.
- The `Serve$lit0` break-on-closed clause is WITHDRAWN, with the true
  loop shape (dead `for {}` break, single-target receive, no `close`
  anywhere in the unit, no reachable exit) and the design consequence
  (the never-exiting Löb instance) recorded in its place. The real
  break-on-closed shape belongs to `Muxer`, outside the client row's
  call graph.
- **Commit-5's message repeats the overclaim** ("async: reachable +
  one small variant"; "meets the close-protocol tier at
  break-on-closed"). History is NOT rewritten — this entry is the
  correction of record, and anyone reading `git log` for the slice
  should read §9 as it now stands instead. Same for commit 3's "§3's
  table built in full" and "standing sequential walks re-validated
  green by this same ci run": corrected in §6's log, message left
  alone.

**Minors.**

- `ChanDMRes`'s module docstring named the DELETED `wpDM_store_step₂`
  among the laws its witness discharges (the stale line was added by
  the very commit that deleted the law). Docstring fixed; §3's plan
  bullet struck.
- `wpDM_eval_boolLit` shipped with no consumer, contradicting §4's
  "every port fires at least once" and `SeqWalkDM`'s "every named
  port". The law has genuine consumer shapes (the muxer rows' loop
  guards and `if`s ARE `Expr.boolLit`), so the anti-scaffold rule's
  DELETE branch does not apply — the honest fix is a witness, and
  `wpDM_eval_boolLit_witness` (a concrete `b = true` assignment walked
  on the DM carrier through the registered port, all premises
  discharged) is it. §3's table now lists the port and its witness.
- §3's port table listed `wpDM_call_start`, which exists nowhere, and
  attributed the two allocating cores to `LangDM.lean` when they are
  in `LawsDM.lean`; §6 claimed the table was "built in full". All
  three corrected in place, with the drop's REASON recorded (the
  nullary call shape needs no start step) — the same treatment §6
  already gave `wpDM_store_step₂`.
- The `go_walk` table-discrimination claim cited evidence that cannot
  support it (standing sequential walks never had the DM entries in
  their import closure, and were replayed from cache rather than
  re-elaborated). §6's log now states the structural argument as
  structural, keeps the no-regression reading of the green walks, and
  names the direction that IS exercised in-build plus the probe that
  would make the remaining direction empirical.
- The dead global `Pos.Countable Nat` instance is DELETED from
  `Specs/ChanDSP.lean` (measured: zero users; ablation elaborates
  byte-identically, while deleting the `Addr` instance fails
  instance synthesis at six sites). §2(a), the commit-4 log and the
  Audit block now credit the `Addr` instance alone.

**Notes.**

- The generic `Persistent (l ↦{.discard} v)` instance moved from the
  target-specific flagship module to `Ghost.lean`, the general
  ghost-state/heap infrastructure module (layering doctrine
  2026-08-01: general proof infrastructure stays separate from
  target-specific infrastructure — before the move, any module wanting
  persistent handle cells had to import the dsp flagship to get it).
- `wpDM_fork_alloc₂`'s discarded `metaToken`s: the deviation from the
  DM kit rule (§3) is now STATED at the law's docstring and in §3.
  Threading them was not taken — it is a statement change to a landed
  law plus its witness, out of scope for a records round — and is
  reversible (the proof already binds both tokens).
- The two receive laws' docstrings now carry the `closed = false`
  scoping clause, and §1 makes that clause a STANDING docstring
  element for delivery laws (the S2 lesson's third occurrence — a rule
  that has to be re-learned every slice belongs in the house
  obligations, not in a per-slice fix).
- FD3: the completion half's provenance is corrected in §10 (it rests
  on the UNDESIGNATED `dspCert400`, not on the designated
  `dspCert`/`dspAllSchedules`), and candidates now have an
  accumulation point in the charter.

**Not re-litigated (the audit re-measured these clean, first-hand):**
`scripts/ci` PASS at the audited tip incl. the Audit gate,
statement-TCB closure and full baseline diff (1483/1483, no
regression); axiom sets FD7-exact by independent `#print axioms`; the
48 designated statements byte-identical; the Audit name-existence
tripwire complete over all five new modules; the parking ledger's
P-CL3-1/3/4/5 entries accurate; every exported triple-carrying
constant carrying its `TerminatesNormallyC` member at the same
env/seed/program; `StepDM`/`StepDC` absent from every statement.

**Gate at the fix tip:** `scripts/ci` green (proofs + docs only; no
`--diff` owed — zero runtime files touched, zero corpus effect), axiom
sets unchanged, 48 designated byte-identical, zero corpus drift.
