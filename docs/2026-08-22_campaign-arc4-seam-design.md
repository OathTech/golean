# Campaign Arc 4 — the interpreter⇄invariant seam: design of record (v1)

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
