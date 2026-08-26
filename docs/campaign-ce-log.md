# Campaign choice-erasure arc — CE lane log (`campaign-ce`)

Worker log for the choice-erasure arc's CE units (plan of record:
`docs/2026-08-27_choice-erasure-arc-plan.md`, v2, professor-reviewed —
read in the `campaign` worktree; it governs this lane). ONE WRITER
(this lane's worker). Sibling lane `campaign-wave-a` owns
`RoundInduction.lean`, `RoundStatement.lean`, `Lens.lean`, and the
kill-list modules — this lane NEVER touches them. This lane's files:
`Frame/ChoiceCanon.lean`, `Frame/ChoiceInv.lean`,
`Frame/ChoiceCanonWitness.lean` (the pinhole witness re-point is CE1
charter work), `Audit/ChoiceInv.lean`, NEW `Frame/SpanIso.lean` +
`Frame/ChoiceVerdict.lean`, plus the minimal consumer edits S3 forces
in `Specs/Raft/SeedPin.lean`/`SeedWitness.lean` and the aggregator
import lines ([AGENT] call CE1-1 below).

## CE1 — the relational face (S3 + SpanIso + the adjusted iff +
verdict invariance) — IN PROGRESS (2026-08-27)

Charter (verbatim constraints in the dispatch, from plan v2 §5-CE1):
1. S3: `CEquivM` gains cleanliness-in-relation; pinhole witness
   re-pointed; SP1 census re-verified through the repaired relation.
2. `SpanIso`: the relational spec of ~ₘ — ∃-bijection on reachable
   spans; MUST NOT quote the canonicalizer; cleanliness explicit as
   relational side conditions; WF premises stated, not baked.
3. The iff in its pre-adjusted form: `Clean ∧ CEquivM ↔ Clean ∧
   SpanIso` on well-formed states. GATE. The unconditioned iff is
   expected FALSE — not attempted.
4. Verdict invariance (completion-and-Result transfer) at the scope
   CE1 can honestly state — SpanIso's first consumer / smoke test.
5. Witnesses throughout; Audit pins; classical-trio or below; zero
   sorry / native_decide / new axioms.

### Reading record (what was read before designing, per dispatch)

Plan v2 (the campaign worktree's
`docs/2026-08-27_choice-erasure-arc-plan.md`); the basecamp review
synthesis (scoff 3b = the flagged-flagged pinhole, §1-S3; §6: the
ChoiceCanon CompCert citation demoted to goal-level "until
cequiv_iff_spanIso exists" — the original scoff-3 substance: the
checker is a decision procedure, not a relational semantics, and
claiming the relational face without the iff is the scoff); the
campaign log's plan-review verdict entry ("execute, with fixes" — the
CE1 gate pre-adjusted, SpanIso must never quote the canonicalizer or
scoff 3 reinstates); SP1's census entries (arc4c log: 171 init draws,
census 108 mapIter@NewRawNode + 30 mapIter + 22 appendSpill@
becomeFollower + 9 appendSpill@NewRawNode + 2 appendSpill@newTwin;
strict ~ held 168/171, REFUTED at exactly 3 — positions 41/98/154,
the persisted `randomizedElectionTimeout` value draws; the one-field
mask's three justification obligations in SeedPin's docstring);
`ChoiceCanon.lean`/`ChoiceInv.lean`/`ChoiceCanonWitness.lean`/
`SeedPin.lean`/`SeedWitness.lean` in full (what the canonicalizer
actually computes); the consumer census (grep: `CEquivM`/`CleanFormM`
consumers = ChoiceCanon/ChoiceInv/ChoiceCanonWitness/Audit/ChoiceInv/
SeedPin/SeedWitness only; RoundInduction mentions the names in
comments only; Challenge/Solution closure has ZERO CE references —
the CE-never-designated rule holds vacuously and must stay so).

### [AGENT] calls, tagged (running list)

- **CE1-1 (file scope):** S3 changes `CEquivM`'s definition, so its
  two out-of-list consumers (`SeedPin.lean`, `SeedWitness.lean` —
  owned by neither lane's list) take MINIMAL mechanical fixes here
  (constructor/accessor adjustments only, no statement redesigns
  beyond what the strengthened relation forces). Rationale: the
  charter's S3 explicitly includes re-verifying the SP1 surface
  through the repaired relation; leaving the build broken for the
  sibling is worse than the small overlap. Wave-a's named files are
  untouched.
- **CE1-2 (S3 shape):** `CEquivM` becomes a structure
  (`eq : canonStateM … = canonStateM …` + `clean :
  (canonStateM …).flags = []`) rather than a bare And — named
  accessors keep consumer proofs legible; right-side cleanliness is
  derived (`clean_right`), not stored, so the relation carries no
  redundant conjunct. `refl` becomes conditional on cleanliness
  (CEquivM is now a PARTIAL equivalence relation — reflexive exactly
  on clean states; that is the pinhole closing, structurally: a
  flagged canonicalization no longer equates even with itself).
- **CE1-3 (pinhole witness):** the flagged-flagged counterexample
  pair is built on the NONBASE-LOC refusal (two observably different
  non-base root locs both serialize `.badLoc` + flag — equal forms,
  flagged): kernel-cheap, and exactly the fail-open-by-forgetting
  shape scoff 3b names. The existing `ChoiceCanonWitness` viewfix
  pair is re-verified DISTINGUISHED under the repaired relation
  (its states are clean; the relation refuses them on content).

### Status blocks (updated as units land — commit hashes recorded
at commit time, never before)

- [x] Reading + consumer census (above)
- [ ] S3: relation repaired + consumers fixed + pinhole witness +
      census re-verification
- [ ] SpanIso statement module (canonicalizer-free)
- [ ] The adjusted iff — THE GATE (proved / resisted-with-finding)
- [ ] Verdict invariance at CE1's honest scope
- [ ] Audit pins + full gate + landing record
