import GoLeanProofs.Specs.GoldenQuorumWP
import GoLeanProofs.Specs.Statements
import GoLeanProofs.Laws.Range

/-!
# Proof-automation arc — phase-0 TARGETS (statements, not results)

Plan of record: `docs/2026-08-01_proof-automation-arc.md`. This module is
the arc's step-0 statement layer: `def … : Prop` targets written before
the machinery that discharges them, plus the phase-2 acceptance criteria
as machine-checked facts rather than prose.

**Provenance, stated plainly** (the quorum pilot's audit finding 6 exists
because this was fudged once): this file lands in the SAME commit as the
phase-1 range rule it also states. The `∀`-config and 3-voter targets
below are genuinely unproven-by-design; `mapIterInvRule_statement` is a
target that is discharged in the same commit (`mapIterInvRule`, from
`Laws/Range.wp_map_iter_inv`) — it is recorded here as a target because
the arc plan lists it as one and because phase 2's automation must keep
its statement fixed, NOT because it was written before its proof.

## What the `∀`-config statement had to solve

`quorumOneKnownFuncSpec` (PROVEN) is a claim about the DRIVER
`committedOneKnown()`, which bakes `MajorityConfig{1:{}}` and
`mapAckIndexer{1:12}` into the program text. There is no `∀ c, acked` in
sight, and no way to put one there: the data is program syntax. Two
routes were considered (arc build log, 2026-08-01):

* **(a) encode the inputs in the HEAP and speak about the METHOD.** State
  `GoSpec` at the callsite of `main.MajorityConfig.CommittedIndex`
  itself, with the receiver and the `AckedIndexer` supplied through the
  caller's environment and heap, and relate that heap footprint to the
  math-level `(c, acked)` by an ENCODING PREDICATE on the map snapshots.
* **(b) a parameterized driver FAMILY**: a function from `(c, acked)` to
  a synthesized driver `Stmt`, quantified over the family.

**(a) is chosen.** Under (b) the theorem's subject would be programs WE
generate, not the vendored etcd-io/raft method — precisely the
over-specialization failure mode the standing check names (the generality
would live in our program generator, not in the claim). Under (a) the
subject is the pinned lowering of the real method, and the quantifier
ranges over inputs the way Go itself does: values in the heap. The
encoding predicate is stated over the map's SNAPSHOT ARRAY (pure data)
rather than as a `Heap → … → Prop` relation, because `GoSpec`'s
`InitialSplit` already quantifies over every heap containing the
footprint — a separate heap-shape relation would re-derive that and add
a second thing to keep in sync.

Cost of (a), recorded as owed: `GoFuncSpec` (unary result) has NO
caller-environment parameter, so a heap-carried receiver is not
denotable through it — the same defect `GoFuncSpec2` was widened to fix
(`Specs/QuorumTargets.lean`). Rather than widen the surface for a
statement nothing discharges yet, the target below is written directly
as the `GoSpec` it unfolds to. When phase 3 discharges it, the natural
refactor is a `GoFuncSpec`-with-`argEnv` (the unary twin of
`GoFuncSpec2`); that widening is owed, not forgotten.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Iris GoLean.Iris.GoldenQuorum

namespace GoLean.Quorum

/-! ## TARGET 1 — the arc's GOAL: `CommittedIndex` for EVERY config

The encoding predicates (`EncodesConfig`/`EncodesAcked`), `configPre`,
the `∀`-config statement itself and the 3-voter instance data moved to
`Specs/Statements.lean` — the Iris-free statement layer (comparator-judge
sprint, 2026-08-02): headline statements must be importable without Iris
in the import closure. The non-vacuity/consistency THEOREMS about them
stay here, with the provenance record above. -/

/-! ### Non-vacuity of the ∀-config statement's HYPOTHESES

A `∀`-statement over encodings is worthless if no encoding exists. These
exhibit one (the 3-voter instance the next target names, data in
`Specs/Statements.lean`), so the target is not satisfiable by an empty
premise set. -/

theorem encodesConfig_three : EncodesConfig threeConfigEntries [1, 2, 3] := by
  refine ⟨?_, ?_, rfl⟩
  · intro p hp
    have hp' : p = ((GoValue.int 1 .uint64), (GoValue.struct ⟨"struct{}"⟩ #[]))
        ∨ p = ((GoValue.int 2 .uint64), (GoValue.struct ⟨"struct{}"⟩ #[]))
        ∨ p = ((GoValue.int 3 .uint64), (GoValue.struct ⟨"struct{}"⟩ #[])) := by
      simpa [threeConfigEntries] using hp
    rcases hp' with rfl | rfl | rfl
    · exact ⟨1, by omega, rfl, rfl, by simp⟩
    · exact ⟨2, by omega, rfl, rfl, by simp⟩
    · exact ⟨3, by omega, rfl, rfl, by simp⟩
  · intro v hv
    have hv' : v = 1 ∨ v = 2 ∨ v = 3 := by simpa using hv
    rcases hv' with rfl | rfl | rfl
    · exact ⟨((GoValue.int 1 .uint64), (GoValue.struct ⟨"struct{}"⟩ #[])),
        Array.mem_def.mpr (by simp [threeConfigEntries]), rfl⟩
    · exact ⟨((GoValue.int 2 .uint64), (GoValue.struct ⟨"struct{}"⟩ #[])),
        Array.mem_def.mpr (by simp [threeConfigEntries]), rfl⟩
    · exact ⟨((GoValue.int 3 .uint64), (GoValue.struct ⟨"struct{}"⟩ #[])),
        Array.mem_def.mpr (by simp [threeConfigEntries]), rfl⟩

/-- **The value the ∀-config target must produce at the 3-voter
instance**, from the reference — `rfl`, so it is a computation. Sorted
acks are `[5,6,12]` and `pos = 3 - (3/2+1) = 1`. -/
theorem committedIndexRef_threeAll :
    committedIndexRef [1, 2, 3] ackedThreeAll = 6 := rfl

/-- ... and it satisfies the declarative spec (committedness AND
maximality, the `∀ j` discharged by case analysis on the thresholds). -/
theorem isCommittedIndex_threeAll :
    IsCommittedIndex [1, 2, 3] ackedThreeAll 6 := by
  refine Or.inr ⟨by decide, by decide, ?_⟩
  intro j hj
  have h1 : ¬ (j ≤ 5) := by omega
  have h2 : ¬ (j ≤ 6) := by omega
  by_cases h3 : j ≤ 12 <;>
    simp [supporters, ackedThreeAll, ackedOrZero, List.filter, h1, h2, h3,
      quorumSize]

/-- Negative twin (math side): `12`, the LARGEST acked index, is not the
committed one — only one voter supports it. The guard against a proof
that reads "returns some acked value". -/
theorem not_isCommittedIndex_threeAll_12 :
    ¬ IsCommittedIndex [1, 2, 3] ackedThreeAll 12 := by
  rintro (⟨h, -⟩ | ⟨-, hq, -⟩)
  · simp at h
  · revert hq
    decide

/-- Negative twin (math side): `5` is not committed either — maximality
fails at `6`. -/
theorem not_isCommittedIndex_threeAll_5 :
    ¬ IsCommittedIndex [1, 2, 3] ackedThreeAll 5 := by
  rintro (⟨h, -⟩ | ⟨-, -, hmax⟩)
  · simp at h
  · exact absurd (hmax 6 (by omega)) (by decide)

end GoLean.Quorum

namespace GoLean.Surface

open GoLean.GoCore GoLean.Quorum

/-! ## TARGET 2 — the 3-voter CONCRETE instance

`quorumThreeAllFuncSpec_statement` and `quorumThreeAllNotTwelve_statement`
moved to `Specs/Statements.lean` (the Iris-free statement layer,
comparator-judge sprint, 2026-08-02). The pin-consistency theorems below
stay with the provenance record. -/

/-- The driver this target names is really in the pinned lowering (and
takes no arguments, so the `GoFuncSpec` shape fits) — `rfl` against the
pin, so editing the pin breaks this. -/
theorem committedThreeAll_in_pin :
    (GoLean.GoCore.findFunctionIn? quorumLowered.funcs
      ⟨"committedThreeAll"⟩).isSome = true := rfl

/-- **The arity check the ∀-config target's shape depends on**, pinned by
`rfl` against the lowering. This is not decoration: the FIRST
`quorumAckedIndexFuncSpec2_statement` was FALSE — not merely unproven —
because it passed the wrong number of arguments, `enterFrame`'s arity
check failed closed, and the configuration was stuck, which falsifies
the judgment's safety half (`ProgressExec` since sem-adequacy slice 4;
`Specs/QuorumTargets.lean`, the recorded correction).
`committedIndexAllConfigs_statement` passes two arguments into two
parameters and one target into one result; that is what this says. -/
theorem committedIndex_arity_in_pin :
    ((GoLean.GoCore.findFunctionIn? quorumLowered.funcs
      ⟨"main.MajorityConfig.CommittedIndex"⟩).map
        (fun f => (f.args.size, f.results.size))) = some (2, 1) := rfl

/-- ... and the parameter/result TYPES the precondition's cells have to
match: a `main.MajorityConfig` receiver, an `AckedIndexer`-INTERFACE
argument (hence the boxed value in `configPre`), and a `main.Index`
result (which frame exit normalizes into the caller's `uint64` cell). -/
theorem committedIndex_types_in_pin :
    ((GoLean.GoCore.findFunctionIn? quorumLowered.funcs
      ⟨"main.MajorityConfig.CommittedIndex"⟩).map
        (fun f => (f.args.toList.map (fun a => a.typ),
                   f.results.toList.map (fun r => r.typ))))
      = some ([.defined ⟨"main.MajorityConfig"⟩,
               .interface ⟨"main.AckedIndexer"⟩],
              [.defined ⟨"main.Index"⟩]) := rfl

end GoLean.Surface

namespace GoLean.Iris

open GoLean.GoCore GoLean.GoCore.Machine

/-! ## TARGET 3 — the inductive range rule's intended statement

Written as a target per the arc plan, and discharged in the same commit
(see the provenance note at the top of this file). Its value from here on
is as a FIXED statement: phase 2's `go_walk` and phase 3's widenings must
keep this shape, and a change to it must be a deliberate, recorded
widening rather than a quiet accommodation. -/

/-- **TARGET 3 (discharged below by `wp_map_iter_inv`)**: the
loop-invariant rule for the nondeterministic key-only map range. One
generic-iteration obligation over an ARBITRARY remaining snapshot and an
ARBITRARY pick, plus the invariant at entry and at exhaustion, entails
the WP of the whole range — independent of the `k!` iteration orders.

Stated over abstract `GF`/`hlc`/stuckness/mask/postcondition so the
statement is a closed `Prop`; it is the exact type of
`Laws/Range.wp_map_iter_inv`. -/
def mapIterInvRule_statement : Prop :=
  ∀ (GF : BundledGFunctors) (hlc : HasLC) (_inst : GoCoreGS hlc GF)
    (s : Stuckness) (E : CoPset) (Φ : Unit → IProp GF)
    (kid : String) (keyTy valTy : Ty) (bodyStmt : Stmt)
    (entries : Array (GoValue × GoValue)) (env : LocalEnv) (k : Cont)
    (I : Array (GoValue × GoValue) → IProp GF),
    (∀ (σ : ExecState), σ.types = GoCoreGS.types GF →
      ∀ p ∈ entries, normalizeValueForTy σ keyTy p.1 = .ok p.1) →
    (∀ (rem : Array (GoValue × GoValue)) (i : Nat) (h : i < rem.size)
        (pa : Addr),
      iprop(I rem
        ∗ pa.id ↦ (⟨some keyTy, (rem[i]'h).1⟩ : HeapCell)
        ∗ (I (rem.eraseIdx i h) -∗
            WP (Config.next (.mapIterK (some kid) none keyTy valTy bodyStmt
                  (rem.eraseIdx i h) env k)) @ s ; E {{ Φ }}))
      ⊢ WP (Config.exec bodyStmt (env.pushScope.declare kid (.base pa))
              (.mapIterK (some kid) none keyTy valTy bodyStmt
                (rem.eraseIdx i h) env k)) @ s ; E {{ Φ }}) →
    iprop(I entries ∗ (I #[] -∗ WP (Config.next k) @ s ; E {{ Φ }}))
      ⊢ WP (Config.next (.mapIterK (some kid) none keyTy valTy bodyStmt
              entries env k)) @ s ; E {{ Φ }}

/-- Target 3 is a THEOREM (proof-automation arc phase 1, same commit).
The `fun … => wp_map_iter_inv …` body is the statement-identity check:
if the rule's shape ever drifts from the stated target, this breaks. -/
theorem mapIterInvRule : mapIterInvRule_statement :=
  fun _GF _hlc _inst _s _E _Φ _kid _keyTy _valTy _body _entries _env _k _I
    hnorm hbody => wp_map_iter_inv hnorm hbody

end GoLean.Iris

namespace GoLean.Surface

/-! ## Phase-2 ACCEPTANCE CRITERIA, as checkable facts

The arc plan's acceptance for `go_walk` is "the existing n = 1 summit
re-proves with IDENTICAL statement and axiom set" (line counts are
advisory). Prose acceptance criteria rot; these do not.

1. **Statement identity** is `summitStatement_pinned` below: the
   re-derived summit must inhabit exactly `quorumOneKnownFuncSpec_statement`.
   Claim strength, stated precisely (audit response 2026-08-01 — the
   original text overclaimed): what the pin CHECKS is that the NAME
   `quorumOneKnownFuncSpec` still resolves, is a theorem, and has the
   type the `def` denotes — since the theorem is already declared at
   that exact type one file earlier, the pin type-checks by unfolding
   the `def` and adds the deletion/rename guard plus a THEOREM-side
   weakening guard (a re-typed `quorumOneKnownFuncSpec` breaks this
   file while its own file still compiles). What it CANNOT catch is a
   DEF-side edit — amending `quorumOneKnownFuncSpec_statement` itself
   together with the proof compiles clean, which is exactly what phase 4
   legitimately did to `committedIndexAllConfigs_statement` (the
   recorded `c.length < 2 ^ 63` correction below); that channel is
   guarded by record, not by the build. The honest phase-2 evidence of
   statement identity is the git-level diff (0 of 32 theorem signatures
   in `GoldenQuorumWP.lean` changed across the rewrite), recorded in the
   arc build log.
2. **Axiom identity** is the `#guard_msgs in #print axioms` gate on
   `quorumOneKnownFuncSpec` in `proofs/Audit.lean`, which must still read
   `[propext, Classical.choice, Quot.sound]` after the re-derivation. A
   tactic that introduced an axiom (or a `native_decide`) would fail that
   gate AND the whole-module sweep.
3. **Coverage identity**: `wp_committedIndex_body` and the body lemmas it
   composes must still be the things being proven — i.e. the tactic
   replaces the WALK, not the claim. Pinned by the `example` reference below.

There is deliberately no line-count assertion: a 100-line bound is a
budget, not a correctness property, and encoding it here would invite
gaming it. -/

/-- **ACCEPTANCE 1 (statement identity)**: the target the phase-2
re-derivation must inhabit, unchanged. -/
def summitStatement_pinned : Prop := quorumOneKnownFuncSpec_statement

/-- **DISCHARGED 2026-08-01 (phase 2, `7fbaf9e`)**: the inhabitation on
the right is now the `go_walk`-derived summit — `quorumOneKnownFuncSpec`'s
walk chain (`wp_oneKnownCall` → … → `wp_committedIndex_body`) is
tactic-driven, with this type unchanged. (Docstring corrected at the
2026-08-01 audit response; the phase-0 text still said the hand-written
walk held it and phase 2 "must reproduce" it.) The type on the left is
what may not change. -/
theorem summitStatement_holds : summitStatement_pinned := quorumOneKnownFuncSpec

/-- **ACCEPTANCE 3 (coverage identity)**: the summit's body walk is still
a theorem about the pinned lowering's `CommittedIndex` body, not a
re-scoped miniature. Referencing it here makes deleting or renaming it a
build failure. -/
example := @GoLean.Iris.GoldenQuorum.wp_committedIndex_body

end GoLean.Surface
