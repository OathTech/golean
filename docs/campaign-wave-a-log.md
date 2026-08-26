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

- **[AGENT] ops note (S1 build):** five consecutive oom-kills at
  the 48G cap during this worktree's FIRST heavy build (cold cache:
  ~145 jobs incl. the Vr/Mar/Vote equation chains) — at default
  threads, at 6, and at 2. Warm-up completed only at
  LEAN_NUM_THREADS=1 (build6, EXIT=0). The recorded "warm at 2"
  remedy is calibrated for the campaign worktree's warm cache, not
  a cold worktree; also: two of the kills were misread at first as
  my own tool-timeout SIGTERMs — `systemctl --user` scope Results
  (oom-kill) are the honest signal, judged per the masked-kill
  convention. Box-wide build-lock observed HELD by
  "coordinator-ceremony" throughout (3+ h, no active build);
  this lane stayed within the explicit-target ≤48G exemption and
  did NOT touch the lock.

- **S2 — RoundFam's family-former slot: EDITED** (RoundStatement +
  SeedPin + the four Round*Lemma closures + one RoundInduction
  docstring). `RoundFam (F : ExecState → Prop) σF := ∃ canon,
  F canon ∧ ∃ r na₀ na fr, FrameSim r na₀ na fr canon σF`; every
  landed instance uses the literal former `(· = canon)`;
  `RoundFam.self σ : RoundFam (· = σ) σ`; the four closure proofs
  gain the `canon', rfl` witness components (mechanical).

- **S4 — the minor batch: EDITED.** (a) `Normalizes` predicate +
  `fieldNormFuel` (kernel-pinned to `typeResolutionFuel - 1` by
  `fieldNormFuel_eq`) wrap the raw 1023 out of L2/L3's premises;
  fuel-monotonicity proved end to end (`normalizeValueForTyFuel_mono`
  + `normalizeListWith_mono`/`normalizeFieldsWith_mono`/
  `normalizeStructValueWith_mono`, plus the `Normalizes.of_le`
  discharge form); Lens builds green standalone. (b)
  `TwinVerdict`/`TwinVerdict.ofResult` decoder beside (NOT inside)
  the pinned T1 statements, with `ofResult_violations` (the decoder
  reads exactly the position `AgreementT1` pins) and
  `agreementT1_verdict` (the aboutness corollary); RaftAgreement
  builds green; Challenge's closure verified untouched (it never
  imports RaftAgreement). (c) the `sliceElems` name collision
  resolved: RoundStatement's private helper renamed
  `twinSliceElems` (the public `GoLean.Lens.sliceElems` keeps the
  name; F5e — no namespace changes).
  [AGENT] validation-batching call: S2+S4 share the RoundStatement
  rebuild cascade (~35 warm modules), so they are validated as ONE
  build at the S4 tip and committed as two slices; risk accepted as
  mechanical-edit-only, recorded here.
  WHAT THIS TAUGHT US: the fuel-monotonicity proof was the entire
  cost of S4a (~150 lines, all mechanical constructor fan-out); the
  professor's "wrap the literal" is cheap ONLY because the
  normalizer's helpers are already parameterized in the recursive
  call — a design worth keeping for every fueled family.
