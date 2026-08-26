# Campaign wave-α log — shape fixes + kills + legibility

Charter source: the basecamp design review (campaign worktree,
`docs/2026-08-27_basecamp-design-review.md` §1 S-fixes + §4 C2/C4)
under the [USER] four-goal frame; dispatched by the campaign
coordinator 2026-08-27. Branch `campaign-wave-a` off main @ c4986b29.
ONE WRITER (this lane). S3/ChoiceCanon/ChoiceInv are the sibling CE1
lane's — NOT touched here.

Units (each its own commit):
- **S1** — FamTrace pairing parameter `R : ExecState → SNet → Prop`
  + `hpair` clause; instantiate `R := fun _ _ => True`; everything
  re-proves verbatim or STOP.
- **S2** — RoundFam family-former slot `F : ExecState → Prop`.
- **S4** — minor batch: `Normalizes` fuel-wrap (Lens L2/L3) +
  monotonicity; `TwinVerdict.ofResult` decoder; `sliceElems` rename.
- **C2** — kills: TwinCheckpoints cluster kill/demote; HandlerEq
  pilot chain demote + tombstone; span_relocate duplicate tag;
  TwinSegs park-closure record.
- **C4** — legibility: live mechanism registry; Corpus/ dir move
  (26 chains); Sym design note to main; Paradoxes.lean; four ledger
  rows.
- **NF** — never-faults statement DRAFT (docs + Prop, NOT designated).

Conventions in force: build-lock, sequential warm after
interface-hot edits (LEAN_NUM_THREADS=2) then scaled full build,
masked-kill exit codes, kernel_rfl never decide, witness-in-same-
slice, computed-vs-literal, zero sorry/native_decide/new axioms,
[AGENT] + what-this-taught-us lines.

## Entries

- **[AGENT] 2026-08-27 — lane opened.** Read the design of record
  (§1/§4), the CE arc plan (boundary check: S3, ChoiceCanon.lean,
  ChoiceInv.lean untouchable here), the mechanism registry (tracked
  copy in this tree). Kill-list details taken from the synthesis §4
  C2 + the charter's expansion; importer counts to be RE-VERIFIED
  against this tree before any deletion, per the deletion-tests-RUN
  convention.

- **S1 — FamTrace pairing parameter: BUILT** (RoundInduction.lean +
  RoundInductionWitness.lean). `FamTrace` gains
  `R : ExecState → SNet → Prop` before `r`, and `cons` gains
  `hpair : R σF' l.N'`; `round_induction`/`seeded_round_induction`
  instantiate `R := fun _ _ => True` (the induction supplies
  `trivial` at each cons); the four trace corollaries
  (`reach`/`flat`/`safety`/`fullInv`) go PARAMETRIC in `R` (none
  reads `hpair`); the five witness statements in
  RoundInductionWitness instantiate `(fun _ _ => True)` textually.
  **Re-proves-verbatim verdict: YES with three mechanical
  arity-only adjustments, zero proof-content changes** — (1) the
  induction's `FamTrace.cons` application gains the literal
  `trivial` argument; (2) `FamTrace.reach`'s and `FamTrace.flat`'s
  induction cons-patterns each gain one positional `_` (the new
  `hpair` field); (3) witness statements gain the `(fun _ _ =>
  True)` instantiation argument. Every proof body is otherwise
  byte-identical; nothing needed re-derivation. Honest docstrings
  updated: O5b now lands BY INSTANTIATION (a strengthened induction
  supplying a real `R`), not by five-module migration.
  WHAT THIS TAUGHT US: the professor's prediction held exactly —
  a parameter threaded through an inductive's motive costs
  underscores, not proofs; the expensive-looking migration risk was
  imaginary because no landed consumer destructures `hpair`.
