import GoLean.Interface
import GateA1.Language
import Iris.BI.Lib.GenHeap
import Iris.ProgramLogic.Adequacy
import Iris.Std.GenSetsInstances
import Std.Data.ExtTreeMap

/-! Fractional ownership of real GoCore root cells. Array indices are the
semantic addresses. Field/index paths remain inside the root value: this
first customer owns a whole root cell, not disjoint fields of one cell. -/
namespace GoLean.IrisCustomer
open GoCore GoCore.Machine
open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap

abbrev HeapMap : Type → Type := fun V => Std.ExtTreeMap Nat V compare

def cellsToMap : List HeapCell → Nat → HeapMap HeapCell
  | [], _ => ∅
  | cell :: cells, base => insert (cellsToMap cells (base + 1)) base cell

def heapToMap (heap : Heap) : HeapMap HeapCell := cellsToMap heap.toList 0

theorem cellsToMap_below (cells : List HeapCell) (base k : Nat) (hk : k < base) :
    get? (cellsToMap cells base) k = none := by
  induction cells generalizing base with
  | nil => simp [cellsToMap, get?_empty]
  | cons c cs ih =>
    rw [cellsToMap, get?_insert_ne (by omega)]
    exact ih (base + 1) (by omega)

theorem get?_cellsToMap (cells : List HeapCell) (base k : Nat) :
    get? (cellsToMap cells base) (base + k) = cells[k]? := by
  induction cells generalizing base k with
  | nil => simp [cellsToMap, get?_empty]
  | cons c cs ih =>
    cases k with
    | zero => simp [cellsToMap, get?_insert_eq]
    | succ k =>
      rw [cellsToMap, get?_insert_ne (by omega)]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (base + 1) k

theorem get?_heapToMap (heap : Heap) (k : Nat) :
    get? (heapToMap heap) k = heap[k]? := by
  simpa [heapToMap] using get?_cellsToMap heap.toList 0 k

theorem heapToMap_set (heap : Heap) (a : Nat) (cell : HeapCell) (ha : a < heap.size) :
    heapToMap (heap.set a cell ha) ≡ₘ insert (heapToMap heap) a cell := by
  intro k
  rw [get?_heapToMap, LawfulPartialMap.get?_insert, get?_heapToMap]
  simp [Array.getElem?_set]

theorem heapToMap_push (heap : Heap) (cell : HeapCell) :
    heapToMap (heap.push cell) ≡ₘ insert (heapToMap heap) heap.size cell := by
  intro k
  rw [get?_heapToMap, LawfulPartialMap.get?_insert, get?_heapToMap]
  simp [Array.getElem?_push, eq_comm]

theorem heapToMap_fresh (heap : Heap) :
    get? (heapToMap heap) heap.size = none := by
  rw [get?_heapToMap]
  simp

end GoLean.IrisCustomer
