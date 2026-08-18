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

## PUBLIC API — the sealed interface (the W6 convention, as in
`SliceMem`/`StepKit`; section added WP arc s3, 2026-08-18)

**What consumers may depend on** (and nothing else), grouped by PROOF
SITUATION; the in-file section headers carry the group numbers.

**Group 1** — *you are naming the bytes behind a Go string*:
`gs` (the `List UInt8` ↔ `GoString` content bridge) with `gs_nil` and
`gs_append` (what turns the machine's `+` into a prefix invariant).

**Group 2** — *you are READING, MEASURING, BUILDING or SLICING a
string value*, each fact conditioned on exactly its bounds/range
hypothesis: `applyStrictOp_stringFromRune_ascii` (`string(rune(c))`
at `c < 128`), `applyStrictOp_indexGet_string` (`s[i]` in bounds),
`applyStrictOp_len_string` (`len(s)`),
`applyStrictOp_slice_string` (`s[lo:hi]`, `lo ≤ hi ≤ len`).

**Internal**: none — this module has no `private` declarations.

**Naming note** (WP arc s3): the kit's vocabulary convention is
`<kind>Cells` for the heap representation and `<kind>Val` for the
handle the program receives (`sliceCells`/`sliceVal`,
`mapCells`/`mapVal`). `gs` is deliberately NEITHER: there is no heap
half to name, and `gs` produces the `GoString` CONTENT that a
`.string` value wraps, not a `GoValue` handle. The short spelling is
also load-bearing — every example keeps its own `gs` def (headline
statements spell `gs`, and no kit name may enter a headline closure,
§12b), and those defs are definitionally this one, so the copies are
zero-proof delegations. Recorded as a reasoned exception rather than
renamed; see `docs/wp-arc-log/s3.md` § The vocabulary family.

**The API discipline** (as `SliceMem`'s, verbatim in substance):

1. Everything here is UNTRUSTED METHOD except `gs`, and even that
   enters a headline only under the §11 statement closure rules — a
   kit lemma NAME never appears in a headline statement (§12b).
2. Additions follow the active-abstraction loop (form note §12): ≥2
   consumers retrofitted in the lifting commit, measured deltas.
   Single-consumer shapes stay private copies in their example
   module with a promotion-ledger row.
3. Lean's `private` hides names without sealing definitional
   transparency; the seal is name-level + this contract.
4. Every public THEOREM above carries an exact `#print axioms` pin in
   `Audit/Kit.lean` § StringMem; `gs` is a vocabulary def, unpinned
   by the standing convention.
5. **Storm/signature discipline: StepKit rules 1–5** (that module's
   `## THE FIVE RULES` section is the kit's single copy — cite, never
   restate). Every fact here states an ABSTRACT `σ : ExecState` and
   returns it unchanged, which is rule 1 in its strongest form: a
   string op touches no cell, so no instantiation of these can put a
   concrete heap front in front of the unifier.

## WHAT LIVES WHERE (the kit map — WP arc s3, 2026-08-18)

THIS module: what the machine computes when the OPERAND is a string.
Values only. No heap half, no stepping, no loop.

Siblings, and the boundary with each:

* `SliceMem` — the identical shape for `[]uint64`, and the module to
  copy when adding a fact here; unlike this one it HAS a heap half
  (`sliceCells`/`storeTarget_*`), because a slice is backed.
* `MapMem` — the identical shape for `map[uint64]uint64`, also
  heap-backed.
* `StepKit` — the machine step that consumes these facts as its
  `applyStrictOp` hypothesis (group 4 there).
* `EntryEq` — its string arm (WP arc s2 item 6) emits entry
  equations whose string cells are `gs`-spelled.

Future `docs/kit-guide.md` (slice 6) section fed by this module:
**Values: strings**.
-/

namespace GoLean.StringMem

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-! ## API group 1 — the string content vocabulary -/

/-- The list↔string value bridge: every string heap cell and every
`+=` rewrite goes through it. -/
def gs (l : List UInt8) : GoString := ⟨⟨l⟩⟩

theorem gs_nil : gs [] = GoString.empty := rfl

/-- String `+` at the list spelling — what turns the append the
machine performs into a pure prefix invariant. -/
theorem gs_append (a b : List UInt8) :
    GoString.append (gs a) (gs b) = gs (a ++ b) := by
  simp [GoString.append, gs]

/-! ## API group 2 — the executable string-op facts -/

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
