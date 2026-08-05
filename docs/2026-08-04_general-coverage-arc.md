# The general-coverage arc — plan of record (2026-08-04)

User direction: the long-term aim is a TOTALLY FAITHFUL Go semantics —
raft is the north star, but the machinery must be Go's, not raft's idiom
list (the standing over-specialization check, promoted to arc goal). This
arc rebalances the implementation frontier toward the general language:
the corpus is already general-Go-shaped (873 cases, 33 categories, only
`quorum` target-specific), so the work is closing the visible red
families, in fundamentality-per-cost order.

Baseline at arc start (`baselines/native-full.tsv`, main @ e8e7ef2):
603/873 PASS. Gap families: generics 0/46; channels 0/38 (its own future
arc); floats 0/20 + complex 2/22; goto/labels/switch ≈25 of
control-flow; embedding/promotion 2/8 + type-switch/interface idioms
(≈28 interface fails); init 0/6; three honest `differential` reds
(BUG-005 live map iteration) and one `nondet` red
(`slices/full-slice-cap-zero`, genuinely choice-dependent cap
observation — the membership-lane motivator).

## Build-right principles (binding for every slice)

- Guardrails first: the red corpus cases EXIST for most features (that
  is what 270 recorded FAILs are); a slice may add edge cases but never
  weakens or rewrites canonical Go to pass.
- Fidelity design notes BEFORE code for anything with modeling latitude
  (floats, generics strategy, membership lane) — decision docs in
  `docs/`, Goose/Perennial comparison where prior art exists.
- Every semantics change: full `scripts/ci --diff`; statement-affecting
  changes: Comparator landmark.
- Fail-closed remains the law: a feature arrives whole or stays
  `frontend-export` red; no silent approximations.
- The de-WF discipline holds for new core code: structural recursion,
  kernel-reducible, no opaque derived instances on semantic paths (the
  `GoValue.eqb` lesson), choices touched only at named sites.
- The nondeterminism doctrine binds
  (`docs/2026-08-04_nondeterminism-doctrine.md`): every new
  choice-consumption site ships a spec-anchored ENVELOPE STATEMENT;
  envelope fidelity is a standing audit dimension; claims stay
  possibilistic. Slice 3 (membership lane) implements the doctrine's
  testing half; the doctrine's concurrency inputs (DRF-SC, -race oracle,
  litmus corpus, fairness quantifier) bind that future arc's design
  note.

## Slices

1. **Sequential control-flow completion.** `switch` evaluation semantics
   (case-expression evaluation order, expressionless switch, fallthrough
   incl. declaring clauses, case-call/panic ordering), labeled
   `break`/`continue` (incl. through defer), `goto` (forward/backward,
   out-of-block/for/switch, over declarations — Go's scoping rules for
   jumps), labeled statements and their scopes. Machine: new/extended
   continuations for labels; frontend lowering for goto/labels. ≈25
   cases. No new heap machinery. This finishes SEQUENTIAL Go control
   before concurrency ever arrives.
2. **Method/field promotion + type switches + assignability riders.**
   BUG-007 (embedding promotion — the 6 `lean-observation` embedding
   reds), type switches (the interface-cluster reds), BUG-011
   (`struct{}{}` assignability — corpus case first, then the
   assignability-aware normalization), the `assert-imported-method-set`
   and `embedded-interface-shadowing` clusters. Closes structs,
   embedding, and most of interfaces.
3. **The membership lane (nondet testing infrastructure).** Design note
   + implementation: for cases whose observable is genuinely
   choice-dependent, the harness checks MEMBERSHIP — Go's observation ∈
   the machine's admitted set (enumerate small stream spaces
   `allStreamsOk`-style; sample `go run` repeatedly where Go itself
   randomizes). Un-reds `slices/full-slice-cap-zero`; establishes the
   oracle pattern concurrency will need (recorded in the sem-adequacy
   arc as the equality→membership weakening). Includes the
   envelope-width review: is any admitted latitude gratuitously wider
   than the Go spec's?
4. **Floats.** Design note FIRST: numerics model (bit-precise IEEE-754
   semantics vs Lean `Float` trust; NaN/±0/rounding observability; what
   the oracle can print), Goose comparison, then implementation. 0/20 →
   target full. `complex` follows the same model in a later slice if the
   note scopes it out.
5. **init ordering.** Package-level variable initialization order +
   `init()` functions (the 6 `lean-observation` reds). Small,
   self-contained. (Landed 2026-08-05, `docs/2026-08-05_init-design.md`,
   branch general-coverage-init: 733 → 747 — the 6 init reds, 7 new
   guardrails, and `control-flow/expressionless-switch-order` green;
   `init/hidden-dep-order` is a designed permanent differential red —
   the spec leaves hidden-dependency init order unspecified and
   go/types' conforming order differs from gc's; recorded in the note
   §1 and `baselines/untriaged-ids`. Zero machine change: globals are
   driver-seeded base cells statically resolved by the frontend.)
6. **Generics.** The largest: design note comparing monomorphization at
   the frontend (keeps GoCore generic-free) vs semantic dictionaries;
   expected outcome is frontend monomorphization with GoCore untouched —
   which keeps the semantic core small and the proof surface stable.
   46 cases + the 4 generic bools. (Decided 2026-08-05, see
   `docs/2026-08-05_generics-design.md`. Correction to this entry's
   original wording: "Goose-style" was inaccurate — present-day Goose
   translates generics POLYMORPHICALLY, so monomorphization is a
   deliberate divergence from Goose, recorded in the note's §6. The
   note also corrects the accounting: 75 generics-blocked reds, of
   which 57 flip on generics alone.)
   (Landed 2026-08-05, branch general-coverage-generics, stages G0–G4
   per the note's §8, build log in its §10: 749 → 823 pass — 63
   pre-existing reds flipped (44 generics + 4 bools + 8 scattered
   builtins/new/variadic + 7 floats/generic-type-set, single-blocked
   once floats landed) plus 12 new guardrail ids (11 green) and 1
   negative probe. GoCore/wire schema untouched; one sanctioned Lean
   rendering fix (`TypeId.unqualified`). Still red with reasons:
   type-parameter-channel-ops (channels arc), type-aliases/struct-literal
   (anonymous non-empty struct — pre-existing gap, the note's flip
   count was over by one), instantiated-type-assert/name (BUG-013, the
   CLI.lean duplicate renderer — charter-deferred one-liner),
   complex/generic-type-set ×9 (complex domain; generics side ready).)

Channels/goroutines remain their own arc (the sem-adequacy arc's
concurrency posture: Choices as scheduler, fork/join statements,
membership oracle from slice 3 of THIS arc).

BUG-005 (live map iteration) is deliberately NOT in this arc: its fix
must replay the snapshot-validation stream-obliviousness analysis
(coupling recorded in BUGS.md) and deserves its own focused slice after
the membership lane exists (its three differential reds are
order-observing by nature).

## Arc completion (2026-08-06)

All six slices landed on `general-coverage` (each through the full
sub-branch cycle: independent 2-reviewer adversarial audit with
refute-by-default verification, audit-response fixes, focused
delta-review(s), fast-forward merge). **603/873 → 837/966**; zero
PASS→FAIL at every one of the ~20 re-pins; pass count strictly
monotone; every new capability's cases classified correctly before its
implementation landed. Every exit criterion below is met; the remaining
129 reds are exactly the recorded non-targets: channels 38+ (own arc),
complex 20 (deferred, floats note §9), range-over-func 9 (Go 1.23
iterators, pre-existing gap), the pre-existing rune-conversion and
tuple-assign backlog clusters, BUG-005's 3 differential reds (deferred
behind the membership lane by plan), BUG-012/BUG-014 pins, and the
designed-red envelope/deviation pins (goto capture/address family,
local-type-argument, hidden-dep-order, to-int-out-of-range,
quarantined-init deps). New bugs filed during the arc: BUG-012
(bare-call discard), BUG-013 (fixed in-arc), BUG-014 (defined-slice/map
nil elements). Flagged for the arc-final audit: the four decided design
notes (floats §11, generics §9, membership lane, init — envelope
statements especially), the hidden-dep-order too-narrow record, and the
membership lane's deferred mechanical-width-certification decision.

## Exit criteria

- Slices 1–2 fully green (control-flow, embedding, interfaces, structs
  categories at or near full pass).
- Membership lane live with `slices/full-slice-cap-zero` green under it
  and the envelope-width review recorded.
- Floats green per the design note's scope; init green.
- Generics: design note landed and decision recorded; implementation
  green or explicitly re-scoped with reasons.
- Zero regressions throughout (the failing-set diff, per slice); pass
  count strictly monotone; every new capability's corpus cases classify
  correctly before its implementation lands.
