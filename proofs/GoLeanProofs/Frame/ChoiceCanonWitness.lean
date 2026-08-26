import GoLeanProofs.Frame.ChoiceCanon
import GoLeanProofs.Sym.KernelRfl

/-! # The view-fixpoint regression witness (arc-4 landing fix round,
2026-08-26)

**What this module witnesses.** The landing audit found a fail-open in
`collectFix`: its stability test compared view-list LENGTHS while
`VSt.bumpView` widens an existing key IN PLACE (filter-and-recons — the
length is unchanged on a widen), so the phase-1 reachability fixpoint
could stop with an untraversed widened window. Phase 2 then emitted
cells whose view/direct facts were never computed, and a cell reachable
only through the untraversed window was silently trimmed — two states
whose zero-like arrays DIFFER IN LENGTH canonicalized EQUAL, clean, no
flag. The fix (`VSt.measure`: key count + total view width + direct
count) makes stability mean "the pass changed nothing".

**The dropped case, concretely** (the exact shape the audit
reconstructed — nested slice aliasing where the widening handle is
discovered in a pass after its container was already visited):

- cell A: array `[slice→B[0,1), slice→C[0,2)]`   (the C-widener sits
  in A's SECOND element, opened only when A's own view widens)
- cell B: array `[slice→A[0,2)]`                 (widens A)
- cell C: array `[int 0, ptr→D]`                 (D reachable ONLY via
  C's second element — inside C's widened window)
- cell D: an all-zero array — length 3 in `wσ3`, length 5 in `wσ5`
- roots: `[slice→C[0,1), slice→A[0,1)]`          (C keyed narrow FIRST,
  so pass 2 visits C before A's element widens it)

Pass 1 keys {C:1, A:2, B:1}; pass 2's ONLY effect is widening C's view
1→2 (C already visited that pass, so its window is not re-walked). The
old length-only test stopped there: D was never marked, phase 2 trimmed
it to `.arr []` (zero-like, length erased), and `wσ3 ~ wσ5` held —
**#eval-confirmed against the pre-fix build** (probe
`tools/campaign/FixCollectFixProbe.lean`: identical clean forms, the
distinguishing projection `[some 2, some 2, some 0, some 1]` on BOTH
sides). Under the fixed measure the fixpoint runs pass 3, marks D
direct, and the two states canonicalize DIFFERENT — witnessed below.

LINEAGE: regression witness for a canonical-labeling traversal
(heap-isomorphism canonicalization); the non-vacuity-gate convention
(witness ships with the fix, same commit). -/

namespace GoLean.Frame.ChoiceErase.ViewFixWitness

open GoLean GoLean.GoCore

/-- The witness state: cells A=0, B=1, C=2, D=3 as in the header;
`dlen` is D's (all-zero) length. -/
def wσ (dlen : Nat) : ExecState :=
  { heap :=
      [ (.base ⟨0⟩, { value := .array #[
            .slice ⟨some (.base ⟨1⟩), 0, 1, 1⟩,
            .slice ⟨some (.base ⟨2⟩), 0, 2, 2⟩] }),
        (.base ⟨1⟩, { value := .array #[
            .slice ⟨some (.base ⟨0⟩), 0, 2, 2⟩] }),
        (.base ⟨2⟩, { value := .array #[
            .int 0 .int, .addr (.base ⟨3⟩)] }),
        (.base ⟨3⟩, { value := .array (Array.replicate dlen (.int 0 .int)) }) ],
    nextAddr := 4 }

def wroots : List GoValue :=
  [ .slice ⟨some (.base ⟨2⟩), 0, 1, 1⟩,
    .slice ⟨some (.base ⟨0⟩), 0, 1, 1⟩ ]

/-- The distinguishing projection: per-cell emitted array length. -/
def cellArrLen : CCell → Option Nat
  | ⟨_, .arr es⟩ => some es.length
  | _ => none

/-- D (discovery id 2) is emitted IN FULL (length 3) — the window the
old fixpoint left untraversed is now collected and D marked direct. -/
theorem viewfix_d3_read :
    (canonState (wσ 3) wroots).cells.map cellArrLen
      = [some 2, some 2, some 3, some 1] := by kernel_rfl

/-- The sibling state differs exactly at D's length. -/
theorem viewfix_d5_read :
    (canonState (wσ 5) wroots).cells.map cellArrLen
      = [some 2, some 2, some 5, some 1] := by kernel_rfl

/-- Both canonicalizations are CLEAN — the refusal channel is not what
distinguishes them; the content is. -/
theorem viewfix_flags_clean :
    ((canonState (wσ 3) wroots).flags, (canonState (wσ 5) wroots).flags)
      = ([], []) := by kernel_rfl

/-- **The regression theorem**: the two states the pre-fix code
silently equated are NOT latitude-equivalent. Under the S3-repaired
relation (cleanliness-in-relation) the pair is distinguished by the
relation's CONTENT half — both forms are clean
(`viewfix_flags_clean`), so the refusal is on the forms differing,
exactly as before S3 (verified at CE1: this proof consumes `h.eq`
and nothing else). -/
theorem viewfix_not_equiv : ¬ CEquiv (wσ 3) wroots (wσ 5) wroots := by
  intro h
  have h' : canonState (wσ 3) wroots = canonState (wσ 5) wroots := h.eq
  have h2 := congrArg (fun f => f.cells.map cellArrLen) h'
  rw [viewfix_d3_read, viewfix_d5_read] at h2
  exact absurd h2 (by decide)

end GoLean.Frame.ChoiceErase.ViewFixWitness

namespace GoLean.Frame.ChoiceErase.PinholeWitness

open GoLean GoLean.GoCore

/-! ## The flagged-flagged pinhole witness (shape fix S3, CE1
2026-08-27 — the basecamp review's scoff 3b, closed structurally)

**What this witnesses.** Before S3, `CEquiv` was BARE form equality;
flags lived inside the form, so two canonicalizations that failed
IDENTICALLY compared equal — the flagged-flagged pinhole
(fail-open-by-forgetting). The pair below realizes it: two states
whose heaps OBSERVABLY DIFFER (a struct field holds `1` vs `2`, and
the machine can read that field through the root loc), rooted at a
NON-BASE loc the canonicalizer refuses (`NONBASE-LOC`). Both
canonicalizations refuse before ever reaching the differing cell, so
the two FORMS are equal — and flagged (`pinhole_forms_equal`,
`pinhole_flagged`). The pre-S3 relation equated the pair
(`pinhole_forms_equal` IS that statement); the repaired relation
REFUSES it structurally: `flags = []` is in the relation
(`pinhole_not_equiv`, discharged from the cleanliness conjunct alone,
no content comparison needed). -/

/-- The pinhole states: one struct cell whose field `x` differs
observably (`1` vs `2`). -/
def pσ (n : Int) : ExecState :=
  { heap := [ (.base ⟨0⟩,
        { value := .struct ⟨"main.T"⟩ #[("x", .int n .int)] }) ],
    nextAddr := 1 }

/-- The root: a NON-BASE loc (a field projection) — the shape the
canonicalizer refuses with `NONBASE-LOC`. -/
def proots : List GoValue :=
  [.addr (.field (.base ⟨0⟩) ⟨"main.T"⟩ "x")]

/-- The shared refused form, as a literal (the computed-vs-literal
standing rule, SP1: NEVER compare two computed forms head-on — the
kernel's lazy defeq on `canonState a ≡ canonState b` with differing
states walks the fueled unfolding pairwise and diverges; measured
here: the head-on statement timed out at default heartbeats and hung
past 100 s at 4M, while each pin below is instant). -/
def pinholeForm : CForm :=
  { roots := [.badLoc], cells := [],
    flags := ["NONBASE-LOC", "NONBASE-LOC"] }

theorem pinhole_pin1 : canonState (pσ 1) proots = pinholeForm := by
  kernel_rfl

theorem pinhole_pin2 : canonState (pσ 2) proots = pinholeForm := by
  kernel_rfl

/-- Both canonicalizations refuse IDENTICALLY: equal forms. This
equality is exactly what the PRE-S3 relation consumed — the pinhole. -/
theorem pinhole_forms_equal :
    canonState (pσ 1) proots = canonState (pσ 2) proots :=
  pinhole_pin1.trans pinhole_pin2.symm

/-- The shared form is FLAGGED (the refusal from phase 1's collection
and phase 2's serialization, one flag entry each): the pair is a
flagged-flagged coincidence, not a clean equivalence. -/
theorem pinhole_flagged :
    (canonState (pσ 1) proots).flags = ["NONBASE-LOC", "NONBASE-LOC"] := by
  rw [pinhole_pin1]; rfl

/-- The states differ OBSERVABLY: the field the root loc names holds
`1` vs `2` (read out through the heap, no canonicalizer involved). -/
def pinholeRead (σ : ExecState) : Option Int :=
  match Heap.lookup σ.heap (.base ⟨0⟩) with
  | some cell =>
      match cell.value with
      | .struct _ fs =>
          match fs[0]? with
          | some (_, GoValue.int v _) => some v
          | _ => none
      | _ => none
  | none => none

theorem pinhole_observably_different :
    pinholeRead (pσ 1) = some 1 ∧ pinholeRead (pσ 2) = some 2 :=
  ⟨rfl, rfl⟩

/-- **The pinhole is CLOSED**: the S3-repaired relation refuses the
pair — from the cleanliness conjunct ALONE (the forms are equal; only
`flags = []` fails). -/
theorem pinhole_not_equiv : ¬ CEquiv (pσ 1) proots (pσ 2) proots := by
  intro h
  have hclean : (canonState (pσ 1) proots).flags = [] := h.clean
  rw [pinhole_flagged] at hclean
  exact absurd hclean (by decide)

end GoLean.Frame.ChoiceErase.PinholeWitness
