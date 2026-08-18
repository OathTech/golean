import GoLean.GoCore.MachineSound

/-!
# StringMem — the string VALUE vocabulary (WP arc s2 item 4)

The kit's string facts, promoted from the two landed copies
(`Examples/StringReverse/Machine.lean`, the witness;
`Examples/WordFreq/Machine.lean`, the second consumer that added the
substring fact). The value bridge `gs` and the conditioned
`applyStrictOp` facts for the string ops the gallery exercises:
`string(rune c))` at ASCII, the in-range byte read `s[i]`, `len(s)`,
and the substring `s[lo:hi]`.

**VALUES ONLY — this module has NO heap half, on purpose** (the
strrev unit's recorded negative finding, g1.md §KIT GAP — StringMem):
a Go string is a pure VALUE in GoCore — no heap backing, so string
reads/`+`/`len` need no `storeTarget`/`Heap.lookup` conditioning
anywhere, and a heap half would be dead weight. Note also that `len`
on a string VALUE reduces definitionally in most positions —
`applyStrictOp_len_string` exists for the conditioned-chain style,
not because `rfl` fails.

Examples keep their own `gs` DEFS (the headline statements spell
`gs` — example-local, so no kit name enters a headline closure, per
the §12b untrusted-method rule); their `gs` is definitionally this
module's, and their fact copies are zero-proof delegations.

Non-consumers, recorded (the ledger's forward list): a non-ASCII
consumer needs the 2/3/4-byte `stringFromRune` arms as separate
conditioned facts; `GoString.compare` facts wait for a string-ordering
consumer.
-/

namespace GoLean.StringMem

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- The list↔string value bridge: every string heap cell and every
`+=` rewrite goes through it. -/
def gs (l : List UInt8) : GoString := ⟨⟨l⟩⟩

theorem gs_nil : gs [] = GoString.empty := rfl

/-- String `+` at the list spelling — what turns the append the
machine performs into a pure prefix invariant. -/
theorem gs_append (a b : List UInt8) :
    GoString.append (gs a) (gs b) = gs (a ++ b) := by
  simp [GoString.append, gs]

/-- `string(rune(c))` at an ASCII code point is the one-byte string.
(The general op is the full UTF-8 encoder; `c < 128` is the
single-byte arm — all the gallery's data exercises.) -/
theorem applyStrictOp_stringFromRune_ascii {σ : ExecState} {c : Nat}
    {ik : IntKind} (h : c < 128) :
    applyStrictOp σ .stringFromRune [.int (c : Nat) ik]
      = .ok (.string (gs [UInt8.ofNat c]), σ) := by
  simp only [applyStrictOp, valueAsInt, bind, Except.bind, pure,
    Except.pure, GoString.fromCodePoint, GoString.fromCodePointNat,
    GoString.utf8Byte, Int.toNat_natCast]
  rw [if_neg (by omega : ¬ ((c : Int) < 0)), if_pos (by omega : c ≤ 0x7f)]
  rfl

/-- `s[i]` on a string VALUE: the in-range byte read, at the `getD`
spelling. Pure — the string is an operand, not a heap cell. -/
theorem applyStrictOp_indexGet_string {σ : ExecState} {l : List UInt8}
    {i : Nat} {ik : IntKind} (hi : i < l.length) :
    applyStrictOp σ .indexGet [.string (gs l), .int (i : Nat) ik]
      = .ok (.int ((l.getD i 0).toNat : Nat) .uint8, σ) := by
  have hneg : ¬ ((i : Int) < 0) := by omega
  have hbyte : (gs l).byte? (i : Int).toNat = some (l.getD i 0) := by
    simp only [GoString.byte?, gs, Int.toNat_natCast]
    rw [List.getElem?_toArray, List.getElem?_eq_getElem hi,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  simp only [applyStrictOp, valueAsInt, stringByteGet, hneg, if_false,
    hbyte, pure, Except.pure, bind, Except.bind]
  rfl

/-- `len(s)` on a string VALUE. -/
theorem applyStrictOp_len_string {σ : ExecState} {l : List UInt8} :
    applyStrictOp σ (.lengthOf (some .string)) [.string (gs l)]
      = .ok (.int (l.length : Nat) .int, σ) := by
  simp only [applyStrictOp, pure, Except.pure, bind, Except.bind]
  rfl

/-- The SUBSTRING fact: `s[lo:hi]` on a string value, in bounds, is
the byte sublist `(l.drop lo).take (hi - lo)` — pure, no allocation
(a Go string slice shares no mutable state the machine models). -/
theorem applyStrictOp_slice_string {σ : ExecState} {l : List UInt8}
    {lo hi : Nat} {ik ik' : IntKind}
    (h1 : lo ≤ hi) (h2 : hi ≤ l.length) :
    applyStrictOp σ (.sliceExpr false)
      [.string (gs l), .int (lo : Nat) ik, .int (hi : Nat) ik']
      = .ok (.string (gs ((l.drop lo).take (hi - lo))), σ) := by
  simp only [applyStrictOp, valueAsInt, bind, Except.bind, pure,
    Except.pure, applySlice, stringSlice, Option.isSome]
  rw [show checkSliceBounds "length" (gs l).length ((lo : Nat) : Int)
        ((hi : Nat) : Int) = .ok (lo, hi) from by
    simp only [checkSliceBounds, gs, GoString.length, List.size_toArray]
    rw [if_neg (by omega : ¬ (((hi : Nat) : Int) < 0)),
      if_neg (by push_cast; omega
        : ¬ (((hi : Nat) : Int) > (l.length : Int))),
      if_neg (by omega : ¬ (((lo : Nat) : Int) < 0)),
      if_neg (by push_cast; omega
        : ¬ (((lo : Nat) : Int) > ((hi : Nat) : Int)))]
    rfl]
  simp only [pure, Except.pure, bind, Except.bind, GoString.slice, gs]
  rw [show (⟨l⟩ : Array UInt8).extract lo hi
      = ⟨(l.drop lo).take (hi - lo)⟩ from by
    apply Array.toList_inj.mp
    simp [List.extract_eq_take_drop]]
  rfl

end GoLean.StringMem
