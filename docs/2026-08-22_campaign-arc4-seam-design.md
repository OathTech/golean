# Campaign Arc 4 — the interpreter⇄invariant seam: design of record (v1)

> **RECONCILIATION (arc-4 landing fix round, 2026-08-26 — the §8
> reconciliation the flexibility redesign queued to "the lane's next
> boundary"; the landing was that boundary and the audit found it
> undone).** This note is SUBORDINATE to
> `docs/2026-08-26_campaign-flexibility-redesign.md` (THE plan of
> record, tracked in this repo since the fix round): the redesign's
> interface stack (I1–I4), its literal-mode stop (§3 I2/§4), and its
> vacuity checks govern; this note remains the record for the
> arm/statement conventions (§4c's R-form flag and the layer
> architecture) as REFINED by the redesign.
>
> **LINEAGE** (added at the fix round per the clever-tricks doctrine,
> which postdates this note by two days): the seam architecture is a
> refinement mapping / forward simulation between the interpreter's
> configurations and abstract network states (Abadi–Lamport), with
> the invariant network carried by inductive invariance — the
> TLA+/IOA refinement-family classics; the certificate-replay layer
> (per-round kernel equations) is standard proof-certificate replay.
> No new mechanism class.

Campaign lane, 2026-08-22, [AGENT] throughout (the architecture is a
judgment call inside §5's delegated proof strategy; anything here that
would change what T1 MEANS is nothing — the statement is pinned and
this note only concerns how it gets proved). Inputs: the T1 statement
(`RaftAgreement.lean`), Arc 3's invariant network over the ported spec
(`VerdiCompat/{RefinedProofStructure,ElectionSafety,CandidateEntries}`,
the invariant index in `docs/campaign-arc3-log.md`), Arc 2's
measurements (711,616-step completing run; kernel:compiled ≥300×), the
compat note's §4c/§4e regrounding architecture, and the kit
(`docs/kit-guide.md`).

## 1. The problem, stated exactly

`AgreementT1` quantifies over ALL choice streams: every completing
interpreter run of the 9.3 MB lowered twin has `violations = 0`. The
∀-side cannot be computed (Arc 2's ladder) and cannot be enumerated
(the stream space is unbounded); it is proved by INDUCTION over the
run. Arc 3's invariant network lives at the SPEC level — Lean
functions ported 1:1 from verdi-raft's handlers, with election safety
etc. proved over abstract network states. The seam is the missing
middle: a simulation between interpreter configurations of the
running lowered twin and abstract network states, strong enough that
the spec-level invariants transfer down to "the in-program checker
never fires."

## 2. The architecture: three layers

**(A) The abstraction function.** `absState : ExecState → Env-shape →
Option AbstractNet` — a TOTAL, first-order reader of the twin's heap
at ROUND BOUNDARIES (the driver's loop head): the three `twinNode`
structs project to abstract per-node raft states; `t.net`/`t.live`
project to the in-flight multiset; the checker's `leaderOf`/`byIndex`
maps project to the ghost-adjacent bookkeeping. `none` = the heap is
not in twin shape (never reachable from the seeded start — an
invariant, not an assumption). This is proof infrastructure, not
statement vocabulary — T1's meaning never touches it (§3.2 layering).

**(B) The per-handler interpreter-run equations** — the campaign's
long middle, and the honest cost center. For each raft-library
handler on the twin's reachable path (the Arc-2 census: 226 static +
9 value-call fids; the HANDLER-level units are ~20: Step/stepLeader/
stepFollower/stepCandidate, handleAppendEntries, handleHeartbeat,
the RequestVote pair, becomeLeader/Follower/Candidate, maybeCommit,
appendEntry, advance/Ready plumbing, the MemoryStorage ops):

> from any interpreter state σ whose `absState σ = some N` and whose
> control sits at the lowered call of handler `h` with decoded
> argument `m`: the run reaches the call's return with state σ' such
> that `absState σ' = some (specHandler h N m)` — the PORTED handler
> applied at the abstract state.

Proved with the KIT (WP walks per handler body — the gallery
mechanism at library scale, `wp_call_enter` family + the Sym
evaluator for straight-line segments), one handler = one unit ≈ one
gallery example's effort (measured precedent: the fib/matmul walks).
These equations are exactly §4c/§4e's "shell node-step DEFINED by
interpreter-run equations on the pinned lowered raft.Step" —
translation-validation shape, done in WP. **W7/SpecTec convergence
(recorded, not assumed): if the SpecTec frontend-correctness route
lands mid-campaign, these equations may become derivable from
AST-level correspondence rather than hand-walked — the unit ladder
below front-loads the highest-value handlers so either future is
served.**

**(C) The round induction.** The driver's loop = deliver-one /
propose / campaign per round; (B)'s equations lift each round to one
abstract net step; Arc 3's `refined_raft_net_invariant` instances hold
along the abstract trace; a final lemma reads the checker: the
in-program S1–S3 checks compute predicates that the spec-level
invariants IMPLY (e.g. `one_leader_per_term_invariant` ⇒ the
`leaderOf`-map disagreement branch is unreachable) — so `violations`
never increments, and any completing run returns 0 at values[0].
The checker-implication lemmas are per-check, small, and are where
the §2.2-item-4 projection is consumed (S2's comparison projected =
the invariant needed is over non-empty EntryNormal (term,data) at
applied indexes — `candidate_entries`/log-matching territory, T3's
lattice feeding T1 exactly as Verdi's decomposition predicts).

## 3. Why this shape (alternatives considered)

- **Direct interpreter induction without the spec layer**: re-derives
  Verdi's whole lattice at machine-state level — strictly more work,
  no reuse of Arc 3, unreadable invariants. Refused.
- **Segment-rfl (Arc 2's route)**: per-concrete-state only — right
  for the ∃-witness, structurally useless for ∀-streams. The two
  arcs stay separate instruments; they share only the reflector.
- **Whole-run WP walk**: the equations ARE WP walks, but scoped
  per-handler with the simulation as the composition frame — the
  only way the walk count stays ~20 instead of per-run-unbounded.

## 4. The unit ladder (Arc 4)

- **A4-U1 (the pilot; next)**: `absState` v1 over the twin's heap
  shape + the SMALLEST handler equation end-to-end —
  `advanceCurrentTerm` or `becomeFollower` (few-line bodies) — to
  validate the proof shape and cost the per-handler unit honestly.
  GO signal: the pilot equation proves with the kit at ≤ a gallery
  example's effort. Anything else → re-design here before more units.
- **A4-U2..U~8**: the message handlers (AppendEntries, Heartbeat,
  RequestVote pair + replies), one per unit, hardest last.
- **A4-U9**: step dispatch + the Ready/harvest plumbing equations.
- **A4-U10**: the round induction + checker-implication lemmas +
  T1 assembly over whatever invariant subset suffices for S1 (S2/S3
  may land as a second wave with T3's lattice).

## 4b. PILOT AMENDMENT (2026-08-22, from A4-U1's verdict — [AGENT])

The pilot validated layer (B)'s equation FORM and refuted its
hand-walk COST (verdict doc on the arc4 lane; headline numbers:
becomeFollower = 3,233 steps / 4 consumed choices; ~9 proof lines
per step at leaf granularity; five kit-less ingredient classes —
struct-normalization preservation, closure call-value enter,
sync-ops, sortSlice, pointer-valued map range — all inside the
SMALLEST handler). Layer (B) is therefore re-based on **the
handler-fragment Sym-evaluator extension**: the mirror evaluator
grows the five ingredient classes (general Go-language machinery,
proofs-side, refinement-theorem-bridged as Sym already is), so a
per-handler equation becomes Sym-driven symbolic execution with
hand proof only at choice points and loop heads. Choice consumption
INSIDE handlers (OQ-C refuted) shapes the equation form: quantify
over the consumed choice prefix, with choice-independent projections
where the pilot's pattern applies. The W7/SpecTec convergence stays
the recorded alternative. Kit lifts for the five classes proceed
regardless (promotion ledger, ≥2-consumer rule trivially met).

## 5. Open questions (logged, none blocking U1)

- OQ-A: `absState` totality vs partiality bookkeeping — Option vs a
  reachability-carried well-formedness pack (the StateWf precedent).
  U1 decides from contact with the heap shape.
- OQ-B: where the equations' "control sits at the lowered call"
  configuration pattern comes from — the kit's call-enter forms
  should give it; if a new Cont-pattern lemma class is needed, it is
  general kit work (promotion ledger), not target infrastructure.
- OQ-C: the mapIter choice site crosses handler boundaries only in
  the DRIVER (the library is map-iteration-free on the census path
  except tracker internals — verify at U1; if a handler consumes
  choices, its equation quantifies over the consumed prefix).
- OQ-D: how much of the S2/S3 checker-implication needs
  `candidate_entries`+log-matching vs what S1 alone needs — scopes
  the first T1 assembly.

## 4c. WAVE-3 ARM CONVENTIONS + THE ROUND SHAPE (2026-08-25, A4-U16 — [AGENT], post-verdict)

The layer-C design of record is
`docs/2026-08-25_campaign-layerc-design.md` (campaign worktree; §5-A1
records the U15 composition verdict and the ROUTE POLICY). This
section holds only the LANE-side conventions that implement it —
one design of record per layer, cited not duplicated.

### Arm-statement conventions (binding for every wave-3 equation)

1. **Route**: literal bounded window chains, one per censused arm
   family (§5-A1 route (i)); the walked route's cost scales with the
   arm's own span (measured: 50 s / 1,710 steps). Landed handler
   equations stay the semantic vocabulary and the validation set —
   never consumed as mid-walk sub-proofs (the U15 instrument wall).
2. **Statement form** (route-independent, the SfHbEquation template):
   drained caller shape `er := <dispatch>(r, m)`; alloc PRIMARY with
   the FrameSim placement quantifier + identity corollary + §3.3
   witness; ∀-stream with the censused choice prefix; conclusions
   ONLY via absState v2 / lens readers / raw renameCell-fixed
   lookups (er) — never literal heaps.
3. **Fixture rules**: a REAL Type cell (the switch driver;
   `absMessage` then reports the true typ — arm records are
   Type-distinguished); caller cells OFF {61, 65} (the
   StaticCellsExt payload rule — [66,69) is the standing placement);
   drop/Stop arms take `staticComplementFull` + nextAddr₀ 98.
4. **The er readout is mandatory** (the shell's own conclusion:
   `Heap.lookup … (.base ⟨r 68⟩) = some ⟨error-iface, v⟩`, transported
   by `FrameSim.lookup_some`; renameCell-fixed for nil and for
   static-cell interface boxes — ErrProposalDropped's box points at
   payload 65 < any na₀, so it rides renaming unchanged).
5. **Norm-wrap depths are store-count-dependent** (U15: Vote norm³ at
   sF arm depth vs norm¹ at handler depth): read the generated
   literal (probe the field) BEFORE stating scalar readouts; collapse
   with `simp only [hvote]`-style side conditions.
6. Counts/addresses as generator-emitted defs (U13 rule, unchanged).

### The round shape (consequence of the verdict, feeding layer C §2-3)

After the FIRST relational join in any composed run, everything
downstream must stay relational/projective; no literal window resumes
mid-walk. Under route (i) this is moot WITHIN a lemma (each round
kind is one literal walk), and binding BETWEEN lemmas: the round
induction composes round LEMMAS at absState level.

**FLAG (refinement to layer-C §2, not a silent divergence):** the
round-lemma form "from any σ at the loop head with `absState σ =
some N`" is not what literal walks deliver — they prove the lemma
from any PLACEMENT (γ-image + FrameSim relocation) of the round's
canonical fixture family. The induction's carried relation `R σ N`
(layer-C §3) must therefore be fixture-family membership (canonical
symbolic state + valuation + placement), with `absState σ = some N`
as its projected READOUT — strictly stronger than the projection
equality alone. This is the same distinction as the handler
equations' fixture-family preconditions, one level up; it costs
nothing on the literal route (the seeded start IS a placement of the
round-0 fixture) but the round-lemma statement should be written in
the R-form from day one. Raised to the layer-C ladder's C1 design
gate.

### The FrameSim-strengthening PROBE (commissioned §5-A1 route (ii); probe-only, nothing ships)

Probe `artifacts/probe/FrameSimStrengthProbe.lean` + greps at tip
d6f0286e; all numbers from runs:

- **Surface**: `GoLeanProofs/Frame/` = 12,661 lines / 22 files;
  FrameSim appears in 15. Conclusion-position (producing)
  occurrences: ~43 — but field-by-field CONSTRUCTION happens in only
  ~6 primitive sites (`setBase`, `alloc_fst`/`alloc_snd`,
  `frameSim_seed`, `frameSim_relocate`, `rebaseSimT`); every other
  producer threads the input pack through packaged relations
  (`ExSim (TripSim …)`, value-pair conjunctions with state riding —
  verified pattern in StrictOps, the heaviest file at 65 mentions).
- **Trial elaboration**: `FrameSimC` (= FrameSim + C1, the domain-
  completeness clause) with `setBaseC` (the canonical in-place-write
  preservation, 14 proof lines) and the zero-seed — clean on first
  full elaboration (one lemma-arity fix), sub-second on warm oleans.
  C1 is CHEAP at the primitive level.
- **THE PROBE'S DESIGN FINDING — C1 alone does not buy the payoff.**
  Completeness makes the relational post-state LOOKUP-determined;
  resuming a literal window needs it LIST-determined. The sufficient
  design is C1 + **C2, the insertion-point shape clause**:
  `σF.heap = renameHeap ρ (take n₀ σ.heap) ++ fr ++ renameHeap ρ
  (drop n₀ σ.heap)` (n₀ = canonical heap length at seed) — preserved
  by BOTH machine mutation kinds (base-keyed `Heap.set` is
  position-preserving; allocation appends to the last segment on
  both sides; the machine never deletes cells), and it pins the
  true state literally, giving the payoff lemma
  `σFfin = γ(S_suffix)` for a generator-emitted suffix literal.
- **Cost vs the ≤2-unit line**: primitives + C2 list algebra +
  payoff lemma ≈ 1 unit; re-elaborating/threading the 12.6k-line
  Frame surface with the extended pack ≈ 0.5–1 unit IF the packaging
  holds everywhere, with risk concentrated in `StepSim`'s induction
  and `StrictOps` — **≈ 2 units nominal, 3 at risk. Verdict:
  BORDERLINE-OVER → per the go/no-go, STAY LITERAL until the
  MsgApp-arm cost trigger fires**; when it does, commission with the
  C1+C2 design (this probe's contribution — U15's route (a) as
  sketched, C1-only, would NOT have sufficed).
