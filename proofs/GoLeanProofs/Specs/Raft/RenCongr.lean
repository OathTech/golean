import GoLeanProofs.Specs.Raft.AbsState
import GoLeanProofs.Frame.Transfer
import GoLeanProofs.Frame.RenameId

/-!
# Rename-congruence lemmas for the abstraction readers (W0 split)

**LINEAGE: separation-logic locality — relocation invariance of pure
heap projections under the executable frame theorem's `FrameSim`
(O'Hearn–Reynolds–Yang; `docs/2026-08-13_executable-frame-theorem.md`).**

Extracted VERBATIM at the W0 reset (kill-list K-C, 2026-08-27) from
the deleted `AllocEq.lean`/`AllocEqWave1.lean` donors: exactly the
renaming-congruence lemmas `AbsStateV2`'s L4 transports consume
(`asU64_ren` is the scalar-decode helper the entry projection needs).
The donors' fixture equations and witnesses are archived at
`archive/fixed-trajectory-era` (docs/ARCHIVE.md); these lemmas are
fixture-independent ∀-shaped machinery — reader congruence, the class
the clean proof plan's frame design (W1) builds on.
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Frame

/-- Scalar decode is loc-free: renaming never changes a `uint64` read. -/
theorem asU64_ren (r : Nat → Nat) (v : GoValue) :
    asU64 (renameValue r v) = asU64 v := by
  cases v <;> simp [renameValue, asU64]

/-- Pointer-scalar dereference commutes with renaming. -/
theorem derefU64_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {v : GoValue} {i : Int} (h : derefU64 σ v = some i) :
    derefU64 σF (renameValue r v) = some i := by
  cases v with
  | nil => simpa [derefU64, renameValue] using h
  | addr l =>
      simp only [derefU64, renameValue]
      simp only [derefU64] at h
      cases hc : Heap.lookup σ.heap l with
      | none => rw [hc] at h; exact absurd h (by simp)
      | some c =>
          rw [hc] at h
          rw [hF.lookup_some hc]
          show asU64 (renameCell r c).value = some i
          rw [show (renameCell r c).value = renameValue r c.value from rfl,
            asU64_ren]
          simpa using h
  | _ => simp [derefU64] at h

/-- One `raftpb.Entry` projection commutes with renaming. -/
theorem absEntry_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {v : GoValue} {p : Int × Int} (h : absEntry σ v = some p) :
    absEntry σF (renameValue r v) = some p := by
  cases v with
  | addr l =>
      simp only [absEntry, renameValue, Option.bind_eq_bind] at h ⊢
      cases hc : Heap.lookup σ.heap l with
      | none => rw [hc] at h; exact absurd h (by simp)
      | some c =>
          rw [hc] at h
          rw [hF.lookup_some hc]
          simp only [Option.bind_some] at h ⊢
          rw [show (renameCell r c).value = renameValue r c.value from rfl]
          split at h
          case _ fs heq =>
            rw [heq]
            simp only [renameValue]
            obtain ⟨idx, hIdx, h⟩ := Option.bind_eq_some_iff.mp h
            obtain ⟨vi, hvi, hdi⟩ := Option.bind_eq_some_iff.mp hIdx
            obtain ⟨tm, hTm, h⟩ := Option.bind_eq_some_iff.mp h
            obtain ⟨vt, hvt, hdt⟩ := Option.bind_eq_some_iff.mp hTm
            simp only [structFieldsLookup_ren, hvi, hvt,
              Option.map_some, Option.bind_some,
              derefU64_ren hF hdi, derefU64_ren hF hdt]
            simpa using h
          case _ => exact absurd h (by simp)
  | _ => simp [absEntry] at h

/-- Renamed backing-array access. -/
theorem renArray_getElem?_ren (r : Nat → Nat) (vs : Array GoValue)
    (i : Nat) :
    ((renameValueList r vs.toList).toArray)[i]?
      = vs[i]?.map (renameValue r) := by
  rw [renameValueList_eq_map]
  simp

/-- The entries walk commutes with renaming (induction over the
window length). -/
theorem absEntsFrom_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    (vs : Array GoValue) :
    ∀ (n i : Nat) {ps : List (Int × Int)},
      absEntsFrom σ vs i n = some ps →
      absEntsFrom σF ((renameValueList r vs.toList).toArray) i n
        = some ps := by
  intro n
  induction n with
  | zero => intro i ps h; simpa [absEntsFrom] using h
  | succ m ih =>
      intro i ps h
      simp only [absEntsFrom, Option.bind_eq_bind] at h ⊢
      obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rest, hrest, h⟩ := Option.bind_eq_some_iff.mp h
      rw [renArray_getElem?_ren, hv]
      simp only [Option.map_some, Option.bind_some]
      rw [absEntry_ren hF hp]
      simp only [Option.bind_some]
      rw [ih (i + 1) hrest]
      simpa using h

/-- **Storage-projection rename-invariance**: under `FrameSim`, the
`MemoryStorage` entries projection at the relocated address reads the
SAME entry list. One-time; serves every storage-reading handler. -/
theorem absStorageEnts_ren {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF)
    {a : Addr} {es : List (Int × Int)}
    (h : absStorageEnts σ a = some es) :
    absStorageEnts σF ⟨r a.id⟩ = some es := by
  unfold absStorageEnts at h ⊢
  simp only [Option.bind_eq_bind] at h ⊢
  cases hc : Heap.lookup σ.heap (.base a) with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c =>
      rw [hc] at h
      have hlk : Heap.lookup σF.heap (.base ⟨r a.id⟩)
          = some (renameCell r c) := hF.lookup_some (l := .base a) hc
      rw [hlk]
      simp only [Option.bind_some] at h ⊢
      rw [show (renameCell r c).value = renameValue r c.value from rfl]
      split at h
      case _ fs heq =>
        rw [heq]
        simp only [renameValue]
        rw [structFieldsLookup_ren]
        split at h
        case _ sv hsv =>
          rw [hsv]
          simp only [Option.map_some, renameValue]
          obtain ⟨base, hbase, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨arrCell, harr, h⟩ := Option.bind_eq_some_iff.mp h
          rw [hbase]
          simp only [Option.map_some, Option.bind_some]
          rw [hF.lookup_some harr]
          simp only [Option.bind_some]
          rw [show (renameCell r arrCell).value
            = renameValue r arrCell.value from rfl]
          split at h
          case _ vs heqa =>
            rw [heqa]
            simp only [renameValue]
            exact absEntsFrom_ren hF vs sv.len sv.offset h
          case _ => exact absurd h (by simp)
        case _ => exact absurd h (by simp)
      case _ => exact absurd h (by simp)

/-! ## W1: the pilot reader's whole-projection frame congruence
(clean-proof plan §W1 "reader-congruence lemmas"; design note
`docs/2026-08-27_w1-judgment-design.md` §3: pre/postconditions in
reader vocabulary transport through FrameSim because scalar readers
are rename-invariant — the footprint design's Spec-transport half). -/

/-- Field read + `uint64` decode commutes with renaming. -/
theorem fieldU64_ren (r : Nat → Nat) (fs : Array (String × GoValue))
    (n : String) :
    fieldU64 ((renameValueFields r fs.toList).toArray) n
      = fieldU64 fs n := by
  unfold fieldU64
  rw [structFieldsLookup_ren]
  cases StructFields.lookup fs n with
  | none => rfl
  | some v => simp [Option.bind, asU64_ren]

/-- **The raft-node projection is footprint-local**: a `FrameSim`
image reads back the SAME abstract state at the renamed root — the
frame theorem's Spec-transport half for the pilot's reader. -/
theorem absRaftNode_frameSim {r : Nat → Nat} {na₀ na : Nat} {fr : Heap}
    {σ σF : ExecState} (hF : FrameSim r na₀ na fr σ σF) (a : Nat)
    {st : AbsRaftState} (h : absRaftNode σ ⟨a⟩ = some st) :
    absRaftNode σF ⟨r a⟩ = some st := by
  unfold absRaftNode at h ⊢
  cases hc : Heap.lookup σ.heap (.base ⟨a⟩) with
  | none => rw [hc] at h; cases h
  | some c =>
      rw [hc] at h
      have hcF := hF.lookup_some hc
      simp only [renameLoc] at hcF
      rw [hcF]
      simp only [Bind.bind, Option.bind] at h ⊢
      split at h
      case h_2 => cases h
      case h_1 fs heq =>
        have hval : (renameCell r c).value
            = .struct ⟨"raft.raft"⟩ ((renameValueFields r fs.toList).toArray) := by
          simp [renameCell, heq, renameValue]
        rw [hval]
        simp only [fieldU64_ren]
        cases hterm : fieldU64 fs "Term" with
        | none => rw [hterm] at h; cases h
        | some term =>
          rw [hterm] at h
          cases hvote : fieldU64 fs "Vote" with
          | none => rw [hvote] at h; cases h
          | some vote =>
            rw [hvote] at h
            cases hlead : fieldU64 fs "lead" with
            | none => rw [hlead] at h; cases h
            | some lead =>
              rw [hlead] at h
              cases hstate : fieldU64 fs "state" with
              | none => rw [hstate] at h; cases h
              | some state =>
                rw [hstate] at h
                simp only [Bind.bind, Option.bind] at h ⊢
                rw [structFieldsLookup_ren]
                split at h
                case h_2 => cases h
                case h_1 rl hrl =>
                  rw [hrl]
                  simp only [Option.map_some, renameValue]
                  cases hrc : Heap.lookup σ.heap rl with
                  | none => rw [hrc] at h; cases h
                  | some rlc =>
                    rw [hrc] at h
                    rw [hF.lookup_some hrc]
                    simp only [Bind.bind, Option.bind] at h ⊢
                    split at h
                    case h_2 => cases h
                    case h_1 rfs hrfs =>
                      have hrval : (renameCell r rlc).value
                          = .struct ⟨"raft.raftLog"⟩
                            ((renameValueFields r rfs.toList).toArray) := by
                        simp [renameCell, hrfs, renameValue]
                      rw [hrval]
                      simp only [fieldU64_ren]
                      exact h

end GoLean.RaftSeam
