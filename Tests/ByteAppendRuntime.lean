import GoLean.GoCore.Machine

namespace GoLean.GoCore.Machine

/-! Frozen pre-optimization operation body, byte copied from c969079a
except this new definition name. -/

def applyStmtOpBeforeByteAppend (s : ExecState) (choices : Choices) (op : StmtOp) (_nt : Nat)
    (vs : List GoValue) : Except Stop (ExecState × Choices) := do
  match op with
  | .appendSlice elem =>
      match vs with
      | [tv, sliceV, elemsV] => do
          let slice ← valueAsSlice sliceV
          let elems ← valueAsSlice elemsV
          validateSlice slice
          validateSlice elems
          let elemValues ← sliceVisibleValues s elems
          let newLen := slice.len + elemValues.size
          let tloc ← valueAsLoc tv
          if newLen <= slice.cap then
            let mut current := s
            let mut i := 0
            for value in elemValues do
              match slice.base with
              | some base =>
                  current ← storeLoc current
                    (.index base (Int.ofNat (slice.offset + slice.len + i))) value
                  i := i + 1
              | none => stuck s!"cannot append {elemValues.size} element(s) into nil slice in place"
            return ((← storeLoc current tloc (.slice { slice with len := newLen })), choices)
          else
            -- gc's `growslice` refusals (runtime/slice.go:191–252; R16
            -- pin, t5-maxalloc 2026-09-02): the new length overflowing
            -- `int`, or the grown backing's byte size exceeding
            -- `maxAllocBytes`, is the recoverable panic `growslice: len
            -- out of range`. Decided on the NEW LENGTH's byte size, NOT
            -- on the chosen capacity: `applyStmtOp_appendSlice_congr`
            -- (MachineSound) states that the outcome CLASS of a spill is
            -- stream-independent, and a cap-based check would make it
            -- false. Consequence, recorded on R16: gc panics on a
            -- SUPERSET — gc panics iff capmem > maxAlloc with capmem =
            -- roundupsize(nextslicecap(newLen, oldCap)·esize) ≥
            -- newLen·esize, this arm iff newLen ≥ 2^63 ∨ newLen·esize >
            -- 2^48 — so wherever newLen's bytes fit but the grown cap's
            -- (≈1.25×) do not, gc raises a recoverable `runtime.Error`
            -- where this arm allocates. That band is a DETERMINISTIC-
            -- PANIC RESIDUAL of fidelity decision 5(b) (observed ∉
            -- modeled; gc never reaches the allocator there, so it is
            -- NOT an allocation failure and NOT under the register #7
            -- rider), unreachable by the corpus (it needs an existing
            -- >2^47-byte slice or `unsafe.Slice`; gc probe append-
            -- growth-over-unsafe is the witness); the in-place path is
            -- never checked (gc calls no growslice there).
            let elemSize ← tySizeBytes s.types elem
            if newLen ≥ intExclusiveUpperBound || newLen * elemSize > maxAllocBytes then
              panic "runtime error: growslice: len out of range"
            let oldValues ← sliceVisibleValues s slice
            -- The capacity ENVELOPE is [newLen, appendSpillUpper] (the
            -- statement and containment argument live on
            -- `appendSpillUpper`, Ops.lean — arc-final audit F2 /
            -- BUG-021, replacing growth+[0,8), which go1.26.5 escapes
            -- in both directions). The choice is offset so the EMPTY
            -- stream (extra = 0) keeps the growth-formula point — the
            -- strict lane's deterministic behavior is unchanged — while
            -- extra ranges bijectively over the whole envelope.
            let width := appendSpillWidth slice.cap newLen
            let (extra, choices) := Choices.consumeAt .appendSpill width choices
            let newCap := newLen +
              ((appendGrowthCap slice.cap newLen - newLen + extra) % width)
            let backing ← buildAppendBackingValue s elem oldValues elemValues newCap
            let (base, current) := s.alloc backing (.array newCap elem)
            return ((← storeLoc current tloc
              (.slice { base := some base, offset := 0, len := newLen, cap := newCap })), choices)
      | _ => stuck "malformed appendSlice operands"
  | op => do return ((← applyStmtOpCore s op vs), choices)


theorem applyStmtOp_byteAppend_exact (s : ExecState) (choices : Choices)
    (op : StmtOp) (nt : Nat) (vs : List GoValue) :
    applyStmtOp s choices op nt vs = applyStmtOpBeforeByteAppend s choices op nt vs := by
  unfold applyStmtOp applyStmtOpBeforeByteAppend
  simp only [ByteArrayStore.appendValuesFast_eq, ByteArrayStore.appendValuesOriginal,
    bind_assoc, pure_bind]
  rfl

end GoLean.GoCore.Machine

namespace GoLean.GoCore.ByteAppendChallenges

open ByteArrayStore

def rawBytes : ExecState :=
  { heap := #[.value (.array 2 (.int .uint8))
      (.array #[.int 256 .uint8, .int 0 .uint8]),
      .value (.int .uint8) (.bool true)] }

theorem first_normalizes_untouched_raw_byte :
    firstByteElement rawBytes ⟨0⟩ 1 (.int (-1) .int) =
      .ok { rawBytes with heap :=
        #[.value (.array 2 (.int .uint8))
            (.array #[.int 0 .uint8, .int 255 .uint8]),
          .value (.int .uint8) (.bool true)] } := by rfl

theorem empty_nil_preserves_malformed_state :
    appendValuesFast rawBytes { base := none, offset := 9, len := 7, cap := 0 } #[] =
      .ok rawBytes := by rfl

theorem first_bounds_precedes_normalization :
    firstByteElement rawBytes ⟨0⟩ (-1) (.bool true) =
      .error (.panic "runtime error: index out of range [-1]") := by rfl

theorem later_store_keeps_bounds_error :
    appendValuesFast rawBytes { base := some (.base ⟨0⟩), offset := 0, len := 1, cap := 9 }
      #[.int 1 .int, .bool true] =
        .error (.panic "runtime error: index out of range [2] with length 2") := by rfl

theorem overwritten_malformed_element_does_not_refuse :
    firstByteElement
      { heap := #[.value (.array 1 (.int .uint8)) (.array #[.bool true])] }
      ⟨0⟩ 0 (.int 258 .int) =
        .ok { heap := #[.value (.array 1 (.int .uint8)) (.array #[.int 2 .uint8])] } := by rfl

theorem untouched_malformed_precedes_bad_incoming :
    firstByteElement
      { heap := #[.value (.array 2 (.int .uint8)) (.array #[.bool true, .int 0 .uint8])] }
      ⟨0⟩ 1 (.bool false) =
        stuck s!"expected uint8 value, got {repr (.bool true : GoValue)}" := by rfl

end GoLean.GoCore.ByteAppendChallenges
