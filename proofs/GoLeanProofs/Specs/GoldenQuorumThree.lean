import GoLeanProofs.Specs.AutomationTargets
import GoLeanProofs.Specs.Statements
import GoLeanProofs.Laws.Values

/-!
# The 3-voter `CommittedIndex` rung (proof-automation arc phase 3,
2026-08-01)

Plan of record: `docs/2026-08-01_proof-automation-arc.md`. This file
discharges `quorumThreeAllFuncSpec_statement`
(`Specs/AutomationTargets.lean`): the pinned lowering of etcd's own
`committedThreeAll` driver — `MajorityConfig{1,2,3}` with
`mapAckIndexer{1:12, 2:5, 3:6}` — returns `6`.

**Why this rung and not just a bigger number.** At n = 3 the map range
has `3! = 6` iteration orders. Walked with `wp_map_iter_next_key` alone
each order is a separate branch; the whole point of
`Laws/Range.wp_map_iter_inv` is that this proof costs ONE generic
iteration plus an invariant. Nothing below enumerates an order.

## The two invariant designs

**The range invariant** (`wp_ci_loop_three`). Over the REMAINING snapshot
`rem`, existentially quantified in two pieces:

* `ks : List Int` — the voter ids still to be visited, with
  `rem = cfgSnapshot ks`. Because `Array.eraseIdx` preserves order, this
  is preserved by exactly one step: `rem.eraseIdx i` is
  `cfgSnapshot (ks.eraseIdx i)`.
* `filled : List Int` — the acked indexes already WRITTEN, most recent
  first. The scratch array is `stkArr ks.length filled trail`: zeros in
  the slots not yet written, then `filled`, then the untouched tail.

and ONE pure relation, order-insensitive by construction:

```
(ks.map ackedOf) ++ filled  ~  allAckedValues
```

— "what is still to come, plus what has been written, is the whole
multiset". A single `List.Perm`, not a set of reachable states: the fill
ORDER is not determined and the invariant never pretends it is. The
iteration variable `i` is `ks.length - 1`, i.e. the position the NEXT
write goes to, which is what makes the write a `list_set_middle` at
`(ks.length - 1)`.

**The sort** (`wp_ci_tail_three`). After the loop `ks = []`, so `filled`
is an arbitrary permutation of `[12, 5, 6]` — the array contents are
genuinely not determined. `Laws/Values.sortLe_pairs_eq_of_perm` says
the machine's sort returns the same list on every permutation of
its input, so the sort's transition is computed ONCE and the six orders
never appear.

## Generality

The per-iteration law `wp_ci_range_body` is stated over an arbitrary
voter id, an arbitrary acked index, an arbitrary `AckedIndexer` snapshot
(with the lookup's answer as a premise, `hpair`), and an arbitrary
scratch-array shape `zeros/filled/trail` over an arbitrary backing-array
length — so it is a law about `majority.go`'s fill loop, not about the
3-voter instance. The 3-voter numbers enter only at the instantiation
sites.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Iris GoLean.Iris.GoldenQuorum

set_option linter.unusedSimpArgs false

namespace GoLean.Iris

open GoLean.Iris.GoldenQuorum

namespace QuorumPin

/-! ## 1. The 3-voter driver, `rfl`-projected out of the pin

`committedThreeAll` is etcd's own `majority_commit.txt` row, vendored in
`Corpus/coverage/exec/quorum/committed-index-real/three-all`. Every lemma
here is `rfl` against `GoldenQuorum.quorumLowered`: edit the pin and they
stop compiling. -/

def threeAllImpl : Func :=
  (findFunctionIn? quorumLowered.funcs ⟨"committedThreeAll"⟩).getD missingFunc

theorem threeAllImpl_find :
    findFunctionIn? quorumLowered.funcs ⟨"committedThreeAll"⟩
      = some threeAllImpl := rfl

theorem threeAllImpl_args : threeAllImpl.args = #[] := rfl

theorem threeAllImpl_results :
    threeAllImpl.results = #[⟨"$res0", .int .uint64⟩] := rfl

/-- `c := MajorityConfig{1: {}, 2: {}, 3: {}}` — one `make` and three
key writes. -/
def taCfgSeq : Stmt :=
  .seqn #[.initialization ⟨"$c31", .map (.int .uint64) (.defined ⟨"struct{}"⟩)⟩,
          .makeMap (.var "$c31") (.int .uint64) (.defined ⟨"struct{}"⟩) none,
          .mapAssign (.var "$c31") (.intLit 1 .uint64)
            (.structLit (.defined ⟨"struct{}"⟩) #[])
            (.int .uint64) (.defined ⟨"struct{}"⟩),
          .mapAssign (.var "$c31") (.intLit 2 .uint64)
            (.structLit (.defined ⟨"struct{}"⟩) #[])
            (.int .uint64) (.defined ⟨"struct{}"⟩),
          .mapAssign (.var "$c31") (.intLit 3 .uint64)
            (.structLit (.defined ⟨"struct{}"⟩) #[])
            (.int .uint64) (.defined ⟨"struct{}"⟩)]

/-- `l := mapAckIndexer{1: 12, 2: 5, 3: 6}`. -/
def taAckSeq : Stmt :=
  .seqn #[.initialization ⟨"$c32", .map (.int .uint64) (.defined ⟨"main.Index"⟩)⟩,
          .makeMap (.var "$c32") (.int .uint64) (.defined ⟨"main.Index"⟩) none,
          .mapAssign (.var "$c32") (.intLit 1 .uint64) (.intLit 12 .uint64)
            (.int .uint64) (.defined ⟨"main.Index"⟩),
          .mapAssign (.var "$c32") (.intLit 2 .uint64) (.intLit 5 .uint64)
            (.int .uint64) (.defined ⟨"main.Index"⟩),
          .mapAssign (.var "$c32") (.intLit 3 .uint64) (.intLit 6 .uint64)
            (.int .uint64) (.defined ⟨"main.Index"⟩)]

def taCallSeq : Stmt :=
  .seqn #[.initialization ⟨"$c33", .int .uint64⟩,
          .call #[.var "$c33"] ⟨"run"⟩ #[.var "$c31", .var "$c32"]]

def taResSeq : Stmt :=
  .seqn #[.assign (.var "$res0") (.var "$c33"), .returnStmt]

theorem threeAllImpl_body_eq :
    threeAllImpl.body = .block #[] #[taCfgSeq, taAckSeq, taCallSeq, taResSeq] :=
  rfl

end QuorumPin

end GoLean.Iris

namespace GoLean.Quorum

open GoLean.GoCore GoLean.Iris

/-! ## 2. The data layer: snapshots, the scratch array, and the invariant

All of it is plain data — no Iris — so the invariant's bookkeeping is
ordinary list reasoning that `omega`/`List.Perm` discharge. -/

/-- A `uint64` GoValue. -/
def u64 (v : Int) : GoValue := .int v .uint64

/-- One `MajorityConfig` map entry: a voter id ↦ the empty struct. -/
def voterEntry (v : Int) : GoValue × GoValue :=
  (u64 v, .struct ⟨"struct{}"⟩ #[])

/-- The map SNAPSHOT a `MajorityConfig` over the voter list `ks` presents
to `mapRangeEntries`. -/
def cfgSnapshot (ks : List Int) : Array (GoValue × GoValue) :=
  (ks.map voterEntry).toArray

/-- The scratch array's value during the fill loop: `zeros` slots not yet
written, then the `filled` values (most recently written first — the fill
runs right to left), then `trail` untouched slots. -/
def stkArr (zeros : Nat) (filled : List Int) (trail : Nat) : GoValue :=
  .array ((List.replicate zeros (u64 0) ++ filled.map u64
            ++ List.replicate trail (u64 0)).toArray)

theorem cfgSnapshot_size (ks : List Int) : (cfgSnapshot ks).size = ks.length := by
  simp [cfgSnapshot]

theorem cfgSnapshot_getElem (ks : List Int) (i : Nat) (h : i < (cfgSnapshot ks).size) :
    (cfgSnapshot ks)[i]'h = voterEntry (ks[i]'(by simpa [cfgSnapshot] using h)) := by
  simp [cfgSnapshot]

theorem cfgSnapshot_eraseIdx (ks : List Int) (i : Nat) (h : i < (cfgSnapshot ks).size) :
    (cfgSnapshot ks).eraseIdx i h = cfgSnapshot (ks.eraseIdx i) := by
  apply Array.toList_inj.mp
  simp [cfgSnapshot, Array.toList_eraseIdx, list_map_eraseIdx]

/-- **The multiset-conservation step.** Erasing position `i` from the
"still to come" list and prepending its value to the "already written"
list preserves the total multiset. This is what makes the range
invariant order-insensitive. -/
theorem perm_eraseIdx_append (t : List Int) :
    ∀ (l : List Int) (i : Nat) (h : i < l.length),
      ((l.eraseIdx i) ++ ((l[i]'h) :: t)).Perm (l ++ t)
  | a :: rest, 0, _ => by
    simp only [List.eraseIdx_cons_zero, List.getElem_cons_zero, List.cons_append]
    exact List.perm_middle
  | a :: rest, i + 1, h => by
    have ih := perm_eraseIdx_append t rest i (by simpa using h)
    simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ, List.cons_append]
    exact ih.cons a
  | [], _, h => absurd h (by simp)


/-! ### The scratch array as a list, and the fill step

`stkArr` is a list of `GoValue`s; the two lemmas below are the shapes the
positional-write law (`Laws/Values.arraySet_middle`) needs on either side
of one write. -/

/-- The scratch array's contents as a list. -/
def stkList (zeros : Nat) (filled : List Int) (trail : Nat) : List GoValue :=
  List.replicate zeros (u64 0) ++ filled.map u64 ++ List.replicate trail (u64 0)

theorem stkArr_eq (zeros : Nat) (filled : List Int) (trail : Nat) :
    stkArr zeros filled trail = .array (stkList zeros filled trail).toArray := rfl

theorem stkList_length (zeros : Nat) (filled : List Int) (trail : Nat) :
    (stkList zeros filled trail).length = zeros + filled.length + trail := by
  simp [stkList]; omega

/-- Every slot holds an already-normalized `uint64` — the premise
`normalizeValueForTy` needs to accept the whole array back unchanged. -/
theorem stkList_normalized {zeros : Nat} {filled : List Int} {trail : Nat}
    (hf : ∀ f ∈ filled, IntKind.uint64.normalize f = f) :
    ∀ x ∈ stkList zeros filled trail,
      ∃ w : Int, x = .int w .uint64 ∧ IntKind.uint64.normalize w = w := by
  intro x hx
  simp only [stkList] at hx
  rcases List.mem_append.1 hx with h | h
  · rcases List.mem_append.1 h with h | h
    · exact ⟨0, List.eq_of_mem_replicate h, by decide⟩
    · obtain ⟨f, hf', rfl⟩ := List.mem_map.1 h
      exact ⟨f, rfl, hf f hf'⟩
  · exact ⟨0, List.eq_of_mem_replicate h, by decide⟩

/-- The unwritten slot the next fill targets, exposed as a `middle`. -/
theorem stkList_succ (zeros : Nat) (filled : List Int) (trail : Nat) :
    stkList (zeros + 1) filled trail
      = List.replicate zeros (u64 0)
        ++ u64 0 :: (filled.map u64 ++ List.replicate trail (u64 0)) := by
  simp [stkList, List.replicate_succ']

/-- ... and the same position after the write. -/
theorem stkList_cons (zeros : Nat) (filled : List Int) (trail : Nat) (v : Int) :
    stkList zeros (v :: filled) trail
      = List.replicate zeros (u64 0)
        ++ u64 v :: (filled.map u64 ++ List.replicate trail (u64 0)) := by
  simp [stkList]

/-- **The slice index's location** — `srt[j]` for a slice over the whole
backing array at offset 0. -/
theorem sliceIndexLoc_base {sta : Addr} {n cap j : Nat} (hj : j < n) (hnc : n ≤ cap) :
    sliceIndexLoc ⟨some (.base sta), 0, n, cap⟩ (j : Int)
      = .ok (.index (.base sta) (j : Int)) := by
  simp only [sliceIndexLoc, validateSlice, if_neg (by omega : ¬ n > cap),
    Bind.bind, Except.bind, pure, Except.pure]
  simp only [if_neg (by omega : ¬ ((j : Int) < 0)),
    Int.toNat_natCast, if_pos hj, Nat.zero_add, Int.ofNat_eq_natCast]

/-- The scratch array's heap cell. -/
def stkCell (cap zeros : Nat) (filled : List Int) (trail : Nat) : HeapCell :=
  ⟨some (.array cap (.int .uint64)), stkArr zeros filled trail⟩

/-- **THE FILL STEP, as a store fact.** Writing `v` through `srt[zeros]`
turns `stkArr (zeros+1) filled trail` into `stkArr zeros (v :: filled) trail`
— the array-level content of one iteration of `majority.go`'s
right-to-left fill. General in the backing array's length, the number of
unwritten slots, the already-written values and the untouched tail. -/
theorem storeLoc_stk_fill {σ : ExecState} {sta : Addr} {zeros trail cap : Nat}
    {filled : List Int} {v : Int}
    (hv : IntKind.uint64.normalize v = v)
    (hf : ∀ f ∈ filled, IntKind.uint64.normalize f = f)
    (hcap : zeros + 1 + filled.length + trail = cap)
    (hlook : Heap.lookup σ.heap (.base sta) = some (stkCell cap (zeros + 1) filled trail)) :
    storeLoc σ (.index (.base sta) (zeros : Int)) (.int v .uint64)
      = .ok { σ with heap := Heap.set σ.heap (.base sta)
                       (stkCell cap zeros (v :: filled) trail) } := by
  have hset : arraySet (stkList (zeros + 1) filled trail).toArray (zeros : Int)
      (.int v .uint64) = .ok (stkList zeros (v :: filled) trail).toArray := by
    rw [stkList_succ, stkList_cons]
    exact arraySet_middle' (by simp) (by simp [u64, coerceStoredValue, hv])
  have hnorm : normalizeValueForTy σ (.array cap (.int .uint64))
      (.array (stkList zeros (v :: filled) trail).toArray)
      = .ok (.array (stkList zeros (v :: filled) trail).toArray) :=
    normalizeValueForTy_intArray
      (by rw [stkList_length]; simp only [List.length_cons]; omega)
      (stkList_normalized (by
        intro f hf'
        rcases List.mem_cons.1 hf' with rfl | hf'
        · exact hv
        · exact hf f hf'))
  have hload : loadLoc σ (.base sta) = .ok (stkArr (zeros + 1) filled trail) := by
    simp only [loadLoc, hlook, stkCell, pure, Except.pure]
  simp only [storeLoc, hload, stkArr_eq, hset, hlook, stkCell, hnorm,
    Bind.bind, Except.bind, pure, Except.pure]

end GoLean.Quorum

namespace GoLean.Iris.GoldenQuorum

/-! ## 3. ONE ITERATION of the voter loop — the general law

`wp_ci_range_body` is the body obligation `Laws/Range.wp_map_iter_inv`
asks for, stated for `majority.go`'s loop at an ARBITRARY voter: an
arbitrary id `q` whose acked index is `v` (the lookup's answer supplied
as `hpair`, over an arbitrary `AckedIndexer` snapshot), and an arbitrary
scratch-array shape — `zeros + 1` slots still unwritten, `filled` already
written, `trail` untouched, in a backing array of any length `cap`. No
config, no voter count and no acked value occurs in it. -/

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open QuorumPin GoLean.Quorum

/-- **The voter loop's BODY, one iteration, at an arbitrary voter** —
`if idx, ok := l.AckedIndex(id); ok { srt[i] = uint64(idx); i-- }` under
the range's per-iteration scope, with the key cell `pa` holding voter
`q`, `i` holding `zeros` (the slot the write targets) and the scratch
array holding `zeros + 1` unwritten slots.

The walk is the arc's semantic centre: the real INTERFACE dispatch
through the `main.AckedIndexer.AckedIndex` anchor into
`main.mapAckIndexer.AckedIndex`, the comma-ok read inside it, the
two-result frame exit, and the store THROUGH A SLICE INDEX into the
backing array — the last one now at a SYMBOLIC index, which is what
`Laws/Values.arraySet_middle` and `storeLoc_stk_fill` exist for. -/
theorem wp_ci_range_body {ia la lba sra sta pa : Addr} {lty : Option Ty}
    {aentries : Array (GoValue × GoValue)} {q v : Int}
    {zeros trail cap slen : Nat} {filled : List Int}
    {rem' : Array (GoValue × GoValue)} {env k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hq : IntKind.uint64.normalize q = q)
    (hv : IntKind.uint64.normalize v = v)
    (hdec : IntKind.int.normalize ((zeros : Int) - 1) = (zeros : Int) - 1)
    (hf : ∀ f ∈ filled, IntKind.uint64.normalize f = f)
    (hcap : zeros + 1 + filled.length + trail = cap)
    (hzlt : zeros < slen) (hsle : slen ≤ cap)
    (hpair : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base lba) = some ⟨lty, .mapData aentries⟩ →
      mapLookupValue σ ⟨some (.base lba)⟩ (.int q .uint64) (.int .uint64)
          (.defined ⟨"main.Index"⟩)
        = .ok (.int v .uint64, true))
    (hl : LocalEnv.lookup env "l" = some (.base la))
    (hsrt : LocalEnv.lookup env "srt" = some (.base sra))
    (hi : LocalEnv.lookup env "i" = some (.base ia)) :
    pa.id ↦ (⟨some (.int .uint64), .int q .uint64⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData aentries⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, slen, cap⟩⟩ : HeapCell)
      ∗ ia.id ↦ (⟨some (.int .int), .int (zeros : Int) .int⟩ : HeapCell)
      ∗ sta.id ↦ stkCell cap (zeros + 1) filled trail
      ∗ (la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
          ∗ lba.id ↦ (⟨lty, .mapData aentries⟩ : HeapCell)
          ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                       .slice ⟨some (.base sta), 0, slen, cap⟩⟩ : HeapCell)
          ∗ ia.id ↦ (⟨some (.int .int), .int ((zeros : Int) - 1) .int⟩ : HeapCell)
          ∗ sta.id ↦ stkCell cap zeros (v :: filled) trail
          -∗ WP (Config.next (.mapIterK (some "id") none (.int .uint64)
                  (.defined ⟨"struct{}"⟩) rangeBody rem' env k))
              @ s ; E {{ Φ }})
      ⊢ WP (Config.exec rangeBody (env.pushScope.declare "id" (.base pa))
            (.mapIterK (some "id") none (.int .uint64)
              (.defined ⟨"struct{}"⟩) rangeBody rem' env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hid, Hl, Hlb, Hsr, Hi, Hst, Hk⟩
  rw [rangeBody_eq]
  go_walk
  unfold ciCallSeq
  go_walk
  -- `var idx main.Index` (named type ⇒ the `σ.types` pin) and `var ok bool`
  go_walk_step (wp_init (v := .int 0 .uint64) (hdef := fun σ ht => by
    rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
      (rfl (a := σ.methods))]
    simp [defaultValue, defaultValueFuel, typeResolutionFuel,
      QuorumPin.typeEnv_Index]))
  go_walk
  go_walk_step (wp_init (v := .bool false) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  -- `idx, ok = l.AckedIndex(id)`: the two targets, the two arguments and the
  -- INTERFACE dispatch (`wp_call_dynamic_enter_ackedIndex`, a registered law)
  go_walk with [hq]
  go_walk_step (wp_ackedIndex_body_entries (mty := lty) (entries := aentries)
    (q := q) (v := v) htypes hq hv hpair)
  go_walk_step (wp_frame_return₂
    (rcell₀ := ⟨some (.defined ⟨"main.Index"⟩), .int v .uint64⟩)
    (rcell₁ := ⟨some .bool, .bool true⟩)
    (tcell₀ := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (tcell₀' := ⟨some (.defined ⟨"main.Index"⟩), .int v .uint64⟩)
    (tcell₁ := ⟨some .bool, .bool false⟩)
    (tcell₁' := ⟨some .bool, .bool true⟩)
    (hstore₀ := fun σ ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, Bind.bind, Except.bind, hv])
    (hstore₁ := fun σ _ht hlk => by
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind, typeResolutionFuel]))
  -- `if ok { srt[i] = uint64(idx); i-- }`
  go_walk
  unfold ciOkIf
  go_walk
  unfold ciOkThen
  go_walk
  -- `&srt[i]` at a SYMBOLIC index: the slice bounds check is a fact about
  -- `zeros`, not a computation, so the walk hands the step back
  go_walk_step (wp_strict_apply_pure
    (out := .addr (.index (.base sta) (zeros : Int)))
    (happly := fun σ => by
      simp [applyStrictOp, valueAsInt,
        sliceIndexLoc_base (sta := sta) (n := slen)
          (cap := cap) (j := zeros) hzlt hsle,
        Bind.bind, Except.bind]))
  go_walk with [hv]
  -- the store THROUGH A SLICE INDEX into the backing array
  go_walk_step (wp_assign_store_loc (a := sta)
    (tgt := .index (.base sta) (zeros : Int))
    (oldcell := stkCell cap (zeros + 1) filled trail)
    (newcell := stkCell cap zeros (v :: filled) trail)
    (fun σ _ht hlk => storeLoc_stk_fill hv hf hcap hlk))
  -- `i--`
  go_walk with [hdec]
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.int .int), .int (zeros : Int) .int⟩)
    (newcell := ⟨some (.int .int), .int ((zeros : Int) - 1) .int⟩)
    (fun σ _ht hlk => by
      have h := storeLoc_int_any (mkind := .int) hlk ((zeros : Int) - 1)
      rw [hdec] at h
      exact h))
  -- unwind the two pushed scopes of the `if` body and the two of the range body
  go_walk_finish Hk

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Iris.GoldenQuorum

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open QuorumPin GoLean.Quorum

/-! ## 4. THE VOTER LOOP, at an arbitrary config — through the inductive
range rule

`wp_ci_loop` covers `var i int; i = n-1; for id := range c { … }` for an
ARBITRARY voter list `ks₀` and an arbitrary acked function `ack`, with
the whole nondeterministic range discharged by ONE generic-iteration
obligation (`wp_ci_range_body`) plus the invariant below. It is the
n-voter law; the 3-voter rung is one instantiation of it and the
`∀`-config theorem will be another.

**THE INVARIANT.** Over the remaining snapshot `rem`:

```
∃ ks filled,
  ⌜rem = cfgSnapshot ks ∧ ks ⊆ ks₀ ∧ (ks.map ack ++ filled) ~ ks₀.map ack⌝
  ∗ … ∗ i ↦ ks.length - 1 ∗ stk ↦ stkArr ks.length filled trail
```

The single `List.Perm` is the whole of the order-insensitivity: what is
still to come (`ks.map ack`) plus what has been written (`filled`) is the
full multiset, and NOTHING says in which order `filled` was built. The
`i` cell is pinned to `ks.length - 1`, the slot the next write targets,
which is exactly what makes the write a positional one. -/
theorem wp_ci_loop {na ca cba la lba sra sta : Addr} {cty lty : Option Ty}
    {ks₀ : List Int} {ack : Int → Int} {aentries : Array (GoValue × GoValue)}
    {trail cap : Nat} {rest env k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hcap : ks₀.length + trail = cap)
    (hsmall : ks₀.length < 2 ^ 63)
    (hnormk : ∀ q ∈ ks₀, IntKind.uint64.normalize q = q)
    (hnormv : ∀ q ∈ ks₀, IntKind.uint64.normalize (ack q) = ack q)
    (hlook : ∀ q ∈ ks₀, ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base lba) = some ⟨lty, .mapData aentries⟩ →
      mapLookupValue σ ⟨some (.base lba)⟩ (.int q .uint64) (.int .uint64)
          (.defined ⟨"main.Index"⟩)
        = .ok (.int (ack q) .uint64, true))
    (hn : LocalEnv.lookup env "n" = some (.base na))
    (hc : LocalEnv.lookup env "c" = some (.base ca))
    (hl : LocalEnv.lookup env "l" = some (.base la))
    (hsrt : LocalEnv.lookup env "srt" = some (.base sra)) :
    na.id ↦ (⟨some (.int .int), .int (ks₀.length : Int) .int⟩ : HeapCell)
      ∗ ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
                  .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData (cfgSnapshot ks₀)⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData aentries⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, ks₀.length, cap⟩⟩ : HeapCell)
      ∗ sta.id ↦ stkCell cap ks₀.length [] trail
      ∗ iprop(∀ filled : List Int,
          ⌜filled.Perm (ks₀.map ack)⌝
            ∗ na.id ↦ (⟨some (.int .int), .int (ks₀.length : Int) .int⟩ : HeapCell)
            ∗ ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
                        .map ⟨some (.base cba)⟩⟩ : HeapCell)
            ∗ cba.id ↦ (⟨cty, .mapData (cfgSnapshot ks₀)⟩ : HeapCell)
            ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                        .interface (.defined ⟨"main.mapAckIndexer"⟩)
                          (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
            ∗ lba.id ↦ (⟨lty, .mapData aentries⟩ : HeapCell)
            ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                         .slice ⟨some (.base sta), 0, ks₀.length, cap⟩⟩ : HeapCell)
            ∗ sta.id ↦ stkCell cap 0 filled trail -∗
          WP (Config.next (.seq rest env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciLoopBlock env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hn, Hc, Hcb, Hl, Hlb, Hsr, Hst, Hcont⟩
  have hdecn : IntKind.int.normalize ((ks₀.length : Int) - 1)
      = (ks₀.length : Int) - 1 := int_normalize_of_range (by omega) (by omega)
  rw [ciLoopBlock_eq]
  go_walk
  unfold ciIDecl
  go_walk 2
  -- `var i int` — named, because the range's INVARIANT below mentions its cell
  go_walk_step wp_init_int as [ia]
  go_walk with [hdecn]
  -- `i = n - 1`
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int ((ks₀.length : Int) - 1) .int⟩)
    (fun σ _ht hl' => by
      have h := storeLoc_int_any (mkind := .int) hl' ((ks₀.length : Int) - 1)
      rw [hdecn] at h
      exact h)) as [Hi]
  -- the range itself: dispatch, read the map cell, take the snapshot
  rw [rangeStmt_eq]
  go_walk
  go_walk_step (wp_map_range_snapshot (ba := cba) (mty := cty)
    (entries := cfgSnapshot ks₀))
  -- THE RANGE, through the INDUCTIVE RANGE RULE
  iapply (wp_map_iter_inv
    (I := fun rem => iprop(∃ ks : List Int, ∃ filled : List Int,
      ⌜rem = cfgSnapshot ks ∧ (∀ x ∈ ks, x ∈ ks₀)
        ∧ ((ks.map ack) ++ filled).Perm (ks₀.map ack)⌝
      ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData aentries⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, ks₀.length, cap⟩⟩ : HeapCell)
      ∗ ia.id ↦ (⟨some (.int .int), .int ((ks.length : Int) - 1) .int⟩ : HeapCell)
      ∗ sta.id ↦ stkCell cap ks.length filled trail))
    (hnorm := fun σ _htypes p hp => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (by simpa [cfgSnapshot] using hp)
      simp [voterEntry, u64, normalizeValueForTy, normalizeValueForTyFuel,
        hnormk x hx, typeResolutionFuel])
    (Hbody := by
      intro rem i hidx pa
      iintro ⟨⟨%ks, %filled, %hpure, Hl, Hlb, Hsr, Hi, Hst⟩, Hid, Hk⟩
      obtain ⟨hrem, hsub, hperm⟩ := hpure
      subst hrem
      have hik : i < ks.length := by
        rw [cfgSnapshot_size] at hidx; exact hidx
      have hqmem : ks[i] ∈ ks₀ := hsub _ (List.getElem_mem hik)
      -- lengths: the perm fixes `ks.length + filled.length = ks₀.length`
      have hlen : ks.length + filled.length = ks₀.length := by
        have := hperm.length_eq
        simp only [List.length_append, List.length_map] at this
        omega
      obtain ⟨m, hm⟩ : ∃ m, ks.length = m + 1 := ⟨ks.length - 1, by omega⟩
      have herase : (ks.eraseIdx i).length = m := by
        rw [List.length_eraseIdx, if_pos hik]; omega
      -- the values already written are acked values, hence normalized
      have hfil : ∀ f ∈ filled, IntKind.uint64.normalize f = f := by
        intro f hf
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1
          (hperm.mem_iff.mp (List.mem_append_right _ hf))
        exact hnormv x hx
      have hicast : ((ks.length : Int) - 1) = (m : Int) := by omega
      rw [cfgSnapshot_getElem, cfgSnapshot_eraseIdx, hicast,
        show stkCell cap ks.length filled trail
          = stkCell cap (m + 1) filled trail from by rw [hm]]
      simp only [voterEntry, u64]
      iapply (wp_ci_range_body (ia := ia) (la := la) (lba := lba) (sra := sra)
        (sta := sta) (pa := pa) (lty := lty) (aentries := aentries)
        (q := ks[i]) (v := ack ks[i]) (zeros := m) (trail := trail) (cap := cap)
        (slen := ks₀.length) (filled := filled) hprog hmeths htypes
        (hnormk _ hqmem) (hnormv _ hqmem)
        (int_normalize_of_range (by omega) (by omega))
        hfil (by omega) (by omega) (by omega)
        (hlook _ hqmem)
        (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
          Scope.lookup, hl])
        (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
          Scope.lookup, hsrt])
        (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
          Scope.lookup]))
      -- the key cell, the loop cells, and the continuation
      iframe
      iintro ⟨Hl, Hlb, Hsr, Hi, Hst⟩
      iapply Hk
      iexists (ks.eraseIdx i)
      iexists (ack ks[i] :: filled)
      isplitl []
      · ipureintro
        refine ⟨rfl, fun x hx => hsub x (List.mem_of_mem_eraseIdx hx), ?_⟩
        refine List.Perm.trans ?_ hperm
        have := perm_eraseIdx_append filled (ks.map ack) i
          (by simpa using hik)
        rw [list_map_eraseIdx, List.getElem_map] at this
        exact this
      · rw [herase, show ((m : Int) - 1) = ((m : Int) - 1) from rfl]
        iframe))
  -- the invariant at ENTRY
  isplitl [Hl Hlb Hsr Hi Hst]
  · iexists ks₀
    iexists ([] : List Int)
    isplitl []
    · ipureintro
      exact ⟨rfl, fun _ h => h, by simp⟩
    · iframe
  · iintro ⟨%ks, %filled, %hpure, Hl, Hlb, Hsr, Hi, Hst⟩
    obtain ⟨hrem, -, hperm⟩ := hpure
    obtain rfl : ks = [] := by
      have : (ks.map voterEntry) = [] := by
        have := congrArg Array.toList hrem.symm
        simpa [cfgSnapshot] using this
      simpa using this
    simp only [List.map_nil, List.nil_append] at hperm
    go_walk 1
    iapply Hcont $$ %filled
    isplitl []
    · ipureintro
      exact hperm
    · iframe

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Quorum

open GoLean.GoCore GoLean.Iris

/-- The scratch array at 3 voters, as a literal — `rfl`, so `simp` can
compute the sort's transition on it. -/
theorem stkCell_three (a b c : Int) :
    stkCell 7 0 [a, b, c] 4
      = (⟨some (.array 7 (.int .uint64)),
          .array #[u64 a, u64 b, u64 c, u64 0, u64 0, u64 0, u64 0]⟩ : HeapCell) :=
  rfl

/-- **The sort, order-blind.** The three loaded values are a permutation
of `[12, 5, 6]` and nothing more is known about them; the machine's
the sort nevertheless returns one fixed list, by
`Laws/Values.sortLe_pairs_eq_of_perm`. This is the step that would
otherwise force the six fill orders into the proof. -/
theorem sortLe_three_all {a b c : Int} (hperm : [a, b, c].Perm [12, 5, 6]) :
    sortLe (fun x y => decide (x.1 ≤ y.1))
        ([(a, IntKind.uint64), (b, IntKind.uint64), (c, IntKind.uint64)] :
          List (Int × IntKind))
      = [(5, IntKind.uint64), (6, IntKind.uint64), (12, IntKind.uint64)] := by
  have hp2 : [a, b, c].Perm [5, 6, 12] :=
    hperm.trans (by decide)
  simpa using sortLe_pairs_eq_of_perm (kind := IntKind.uint64) hp2 (by decide)

/-- The three fill values at the 3-voter instance are `12`, `5`, `6` in
some order, so each is a normalized `uint64`. -/
theorem three_all_normalized {a b c : Int} (hperm : [a, b, c].Perm [12, 5, 6]) :
    IntKind.uint64.normalize a = a ∧ IntKind.uint64.normalize b = b
      ∧ IntKind.uint64.normalize c = c := by
  have hmem : ∀ x ∈ [a, b, c], x = 12 ∨ x = 5 ∨ x = 6 := by
    intro x hx
    have := hperm.mem_iff.mp hx
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · rcases hmem a (by simp) with rfl | rfl | rfl <;> decide
  · rcases hmem b (by simp) with rfl | rfl | rfl <;> decide
  · rcases hmem c (by simp) with rfl | rfl | rfl <;> decide

end GoLean.Quorum

namespace GoLean.Iris.GoldenQuorum

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open QuorumPin GoLean.Quorum

/-! ## 5. The tail at n = 3 — `slices.Sort`, `pos`, and the readout

The array the loop leaves holds a PERMUTATION of `[12, 5, 6]` in its
first three slots, and which permutation is genuinely undetermined. The
sort's transition is nevertheless computed once, through
`sortLe_three_all`; after it the array is the literal
`[5, 6, 12, 0, 0, 0, 0]` and the rest of the tail is ordinary walking:
`pos = 3 - (3/2 + 1) = 1` and `srt[1] = 6` — Go's `n/2+1`-th largest. -/
theorem wp_ci_tail_three {na sra sta ra : Addr} {filled : List Int} {env k}
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hperm : filled.Perm [12, 5, 6])
    (hn : LocalEnv.lookup env "n" = some (.base na))
    (hsrt : LocalEnv.lookup env "srt" = some (.base sra))
    (hres : LocalEnv.lookup env "$res0" = some (.base ra)) :
    na.id ↦ (⟨some (.int .int), .int 3 .int⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, 3, 7⟩⟩ : HeapCell)
      ∗ sta.id ↦ stkCell 7 0 filled 4
      ∗ ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 6 .uint64⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec sortStmt env
            (.seq [ciPosStmt, ciResStmt] env k)) @ s ; E {{ Φ }} := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, filled = [a, b, c] := by
    have hlen : filled.length = 3 := by simpa using hperm.length_eq
    match filled, hlen with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  obtain ⟨hna, hnb, hnc⟩ := three_all_normalized hperm
  have hmerge := sortLe_three_all hperm
  rw [stkCell_three]
  iintro ⟨Hn, Hsr, Hst, Hr, Hcont⟩
  -- `slices.Sort(srt)` — the ORDER-BLIND step
  rw [sortStmt_eq]
  go_walk
  go_walk_step (wp_sort_slice (a := sta)
    (oldcell := ⟨some (.array 7 (.int .uint64)),
                 .array #[u64 a, u64 b, u64 c, u64 0, u64 0, u64 0, u64 0]⟩)
    (newcell := ⟨some (.array 7 (.int .uint64)),
                 .array #[u64 5, u64 6, u64 12, u64 0, u64 0, u64 0, u64 0]⟩)
    (happly := by
      intro σ ch _ht hlk
      simp [applyStmtOp, valueAsSlice, validateSlice, sliceIndexLoc, loadLoc,
        hlk, u64, heap_lookup_set_base_self, Bind.bind, Except.bind,
        List.range', List.forIn_cons, List.forIn_nil, arrayGet, arrayIndexNat,
        storeLoc, arraySet, coerceStoredValue, normalizeValueForTy,
        normalizeValueForTyFuel, normalizeListWith, hmerge,
        heap_set_set_of_lookup hlk, Functor.map, Except.map, hna, hnb, hnc,
        show IntKind.uint64.normalize 0 = 0 from by decide,
        show IntKind.uint64.normalize 5 = 5 from by decide,
        show IntKind.uint64.normalize 6 = 6 from by decide,
        show IntKind.uint64.normalize 12 = 12 from by decide, typeResolutionFuel, applyStmtOpCore]))
  -- `pos := n - (n/2 + 1)` — pure integer arithmetic throughout
  go_walk
  rw [ciPosStmt_eq]
  go_walk
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int 1 .int⟩)
    (fun σ _ht hlk => by
      have h := storeLoc_int_any (mkind := .int) hlk 1
      rw [show IntKind.int.normalize 1 = 1 from by decide] at h
      exact h))
  -- `return Index(srt[pos])`
  go_walk
  rw [ciResStmt_eq]
  go_walk
  go_walk_step (wp_strict_apply_read (a := sta)
    (cell := ⟨some (.array 7 (.int .uint64)),
              .array #[u64 5, u64 6, u64 12, u64 0, u64 0, u64 0, u64 0]⟩)
    (out := .int 6 .uint64)
    (happly := fun σ _ht hlk => by
      simp [applyStrictOp, valueAsInt, sliceIndexLoc, validateSlice, loadLoc,
        hlk, u64, arrayGet, arrayIndexNat, Bind.bind, Except.bind]))
  go_walk_step (wp_strict_apply_pin (out := .int 6 .uint64)
    (happly := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [applyStrictOp, convertValueToTy, convertValueToTyFuel,
        typeResolutionFuel, resolveDefinedAliases, resolveDefinedAliasesFuel,
        QuorumPin.typeEnv_Index, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 6 = 6 from by decide]))
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (newcell := ⟨some (.defined ⟨"main.Index"⟩), .int 6 .uint64⟩)
    (fun σ ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 6 = 6 from by decide]))
  go_walk_finish Hcont

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Quorum

open GoLean.GoCore GoLean.Iris GoLean.Iris.GoldenQuorum

/-! ## 6. The 3-voter instance data -/

/-- The acked function of etcd's `committedThreeAll` row. -/
def ack3 : Int → Int := fun x => if x = 1 then 12 else if x = 2 then 5 else 6

theorem cfgSnapshot_three : cfgSnapshot [1, 2, 3] = threeConfigEntries := rfl

theorem map_ack3 : [(1 : Int), 2, 3].map ack3 = [12, 5, 6] := by decide

theorem stkCell_start : stkCell 7 3 [] 4
    = (⟨some (.array 7 (.int .uint64)), QuorumPin.stkZero⟩ : HeapCell) := rfl

/-- The `AckedIndexer` lookup at each of the three voters — the `hlook`
premise of `wp_ci_loop` at this instance. -/
theorem ackedThree_lookup {lba : Addr} {lty : Option Ty} :
    ∀ q ∈ [(1 : Int), 2, 3], ∀ σ : ExecState,
      Heap.lookup σ.heap (.base lba) = some ⟨lty, .mapData threeAckedEntries⟩ →
      mapLookupValue σ ⟨some (.base lba)⟩ (.int q .uint64) (.int .uint64)
          (.defined ⟨"main.Index"⟩)
        = .ok (.int (ack3 q) .uint64, true) := by
  intro q hq σ hl
  have hq' : q = 1 ∨ q = 2 ∨ q = 3 := by simpa using hq
  rcases hq' with rfl | rfl | rfl <;>
    simp [ack3, mapLookupValue, mapEntries, loadLoc, hl, threeAckedEntries,
      mapEntryIndex?, valueEq, valueEqFuel, checkKeyHashable, valueHashability,
      Bind.bind, Except.bind, typeResolutionFuel]

end GoLean.Quorum

namespace GoLean.Iris.GoldenQuorum

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open QuorumPin GoLean.Quorum

/-- `if len(stk) >= n { srt = stk[:n] }` at `n = 3` — still the TAKEN
branch (`7 >= 3`), so the on-stack array is resliced and nothing is
allocated. The resulting slice has length 3 and the array's capacity 7. -/
theorem wp_ci_fitIf_three {na sta sra : Addr} {w : GoValue} {rest env k}
    (hn : LocalEnv.lookup env "n" = some (.base na))
    (hstk : LocalEnv.lookup env "stk" = some (.base sta))
    (hsrt : LocalEnv.lookup env "srt" = some (.base sra)) :
    na.id ↦ (⟨some (.int .int), .int 3 .int⟩ : HeapCell)
      ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkZero⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)), w⟩ : HeapCell)
      ∗ (na.id ↦ (⟨some (.int .int), .int 3 .int⟩ : HeapCell)
          ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkZero⟩ : HeapCell)
          ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                       .slice ⟨some (.base sta), 0, 3, 7⟩⟩ : HeapCell)
          -∗ WP (Config.next (.seq rest env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciFitIf env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hn, Hstk, Hsrt, Hcont⟩
  rw [ciFitIf_eq]
  go_walk
  go_walk_step (wp_strict_apply_read (a := sta)
    (cell := ⟨some (.array 7 (.int .uint64)), stkZero⟩)
    (out := .slice ⟨some (.base sta), 0, 3, 7⟩)
    (happly := fun σ _ht hl => by
      simp [applyStrictOp, applySlice, loadLoc, hl, stkZero, valueAsInt,
        sliceFromArray, checkSliceBounds, Bind.bind, Except.bind]))
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.slice (.int .uint64)), w⟩)
    (newcell := ⟨some (.slice (.int .uint64)),
                 .slice ⟨some (.base sta), 0, 3, 7⟩⟩)
    (fun σ _ht hl => by
      simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind, typeResolutionFuel]))
  go_walk_finish Hcont

/-- **THE `CommittedIndex` BODY WALK AT 3 VOTERS** — the real
`main.MajorityConfig.CommittedIndex` of the pinned etcd-io/raft lowering
on `MajorityConfig{1,2,3}` with `mapAckIndexer{1:12, 2:5, 3:6}`. Every
statement of `majority.go`'s algorithm is walked, with the voter range
discharged by ONE generic iteration (`wp_ci_loop`) and the sort by the
order-blind step. It leaves `6` in the result cell —
`GoLean.Quorum.committedIndexRef [1,2,3] ackedThreeAll`. -/
theorem wp_committedIndex_body_three {ca cba la lba ra : Addr}
    {cty lty : Option Ty} {k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData threeConfigEntries⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData threeAckedEntries⟩ : HeapCell)
      ∗ ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 6 .uint64⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec committedIndexImpl.body
            [[("$res0", Loc.base ra), ("l", Loc.base la), ("c", Loc.base ca)]] k)
          @ s ; E {{ Φ }} := by
  have hsize3 : (Int.ofNat threeConfigEntries.size) = 3 := rfl
  iintro ⟨Hc, Hcb, Hl, Hlb, Hr, Hcont⟩
  rw [committedIndexImpl_body_eq]
  go_walk with [committedIndexStmts_toList]
  -- `n := len(c)`
  go_walk_step (wp_ci_len (cba := cba) (cty := cty)
    (entries := threeConfigEntries) (by decide) rfl) as [na]
  go_walk with [hsize3]
  -- `if n == 0 { return math.MaxUint64 }`, not taken
  go_walk_step (wp_ci_emptyIf (na := na) (n := 3) rfl
    (fun σ => by
      simp [applyStrictOp, valueEq, valueEqFuel, typeResolutionFuel,
        Bind.bind, Except.bind]))
  go_walk
  -- `var stk [7]uint64` and `var srt []uint64`
  go_walk_step wp_ci_stkDecl as [sta]
  go_walk
  go_walk_step wp_ci_srtDecl as [sra]
  go_walk
  -- `if len(stk) >= n { srt = stk[:n] }`, still the reslice branch at n = 3
  go_walk_step (wp_ci_fitIf_three (na := na) (sta := sta) (sra := sra) rfl rfl rfl)
  go_walk
  -- the voter loop: ONE generic iteration + the permutation invariant
  rw [← cfgSnapshot_three, ← stkCell_start]
  go_walk_step (wp_ci_loop (na := na) (ca := ca) (cba := cba) (la := la)
    (lba := lba) (sra := sra) (sta := sta) (cty := cty) (lty := lty)
    (ks₀ := [1, 2, 3]) (ack := ack3) (aentries := threeAckedEntries)
    (trail := 4) (cap := 7)
    hprog hmeths htypes rfl (by decide)
    (fun q hq => by
      have : q = 1 ∨ q = 2 ∨ q = 3 := by simpa using hq
      rcases this with rfl | rfl | rfl <;> decide)
    (fun q hq => by
      have : q = 1 ∨ q = 2 ∨ q = 3 := by simpa using hq
      rcases this with rfl | rfl | rfl <;> decide)
    (fun q hq σ _ht hl => ackedThree_lookup q hq σ hl)
    rfl rfl rfl rfl)
    as [filled, Hperm, Hn2, Hc2, Hcb2, Hl2, Hlb2, Hsr2, Hst2]
  icases Hperm with %hperm
  rw [map_ack3] at hperm
  -- ONE step (`wp_stmt_op_first` matches every `Config.exec`)
  go_walk 1
  -- `slices.Sort`, `pos`, `return Index(srt[pos])`
  go_walk_step (wp_ci_tail_three (na := na) (sra := sra) (sta := sta) (ra := ra)
    (filled := filled) htypes hperm rfl rfl rfl)

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Iris.GoldenQuorum

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open QuorumPin GoLean.Quorum

/-- **The `CommittedIndex` callsite** inside `run`, at 3 voters. -/
theorem wp_committedIndexCall_three {ca cba la lba ta : Addr}
    {cty lty : Option Ty} {env k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hres : LocalEnv.lookup env "$c3" = some (.base ta))
    (hc : LocalEnv.lookup env "c" = some (.base ca))
    (hl : LocalEnv.lookup env "l" = some (.base la)) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData threeConfigEntries⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                  .map ⟨some (.base lba)⟩⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData threeAckedEntries⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 6 .uint64⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec
            (.call #[.var "$c3"] ⟨"main.MajorityConfig.CommittedIndex"⟩
              #[.var "c",
                .toInterface (.interface ⟨"main.AckedIndexer"⟩)
                  (.defined ⟨"main.mapAckIndexer"⟩) (.var "l")]) env k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hc, Hcb, Hl, Hlb, Ht, Hcont⟩
  go_walk
  go_walk_step (wp_strict_apply_pin
    (out := .interface (.defined ⟨"main.mapAckIndexer"⟩)
      (.map ⟨some (.base lba)⟩))
    (happly := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [applyStrictOp, canonicalDynamicTy, canonicalTy, canonicalTyFuel,
        resolveDefinedAliases, resolveDefinedAliasesFuel, typeResolutionFuel,
        QuorumPin.typeEnv_mapAckIndexer, Ty.mentionsUnsupported,
        Bind.bind, Except.bind, Ty.mentionsUnsupportedFuel]))
  go_walk_step (wp_call_enter₂₁ (func := QuorumPin.committedIndexImpl)
    (w₀ := .map ⟨some (.base cba)⟩)
    (w₁ := .interface (.defined ⟨"main.mapAckIndexer"⟩)
      (.map ⟨some (.base lba)⟩))
    (dv₀ := .int 0 .uint64)
    (hfind := by rw [hprog]; exact QuorumPin.committedIndexImpl_find)
    (hargs := QuorumPin.committedIndexImpl_args)
    (hres := QuorumPin.committedIndexImpl_results)
    (hnodisp := fun σ hf hm ht => by
      rw [execState_pin_eq (ht.trans htypes) (hf.trans hprog) (hm.trans hmeths)]
      simp +decide [dynamicDispatch?, methodInfoByFuncId?,
        methodRecvInterfaceName?, resolveDefinedAliases,
        resolveDefinedAliasesFuel, QuorumPin.quorumMethods_eq,
        QuorumPin.typeEnv_MajorityConfig, Bind.bind, Except.bind]
      split <;> rfl)
    (hnorm₀ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_MajorityConfig])
    (hnorm₁ := fun σ _ => by
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel])
    (hdef₀ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [defaultValue, defaultValueFuel, typeResolutionFuel,
        QuorumPin.typeEnv_Index])) as [a₀, a₁, a₂]
  go_walk_step (wp_committedIndex_body_three (ca := a₀) (cba := cba) (la := a₁)
    (lba := lba) (ra := a₂) (cty := cty) (lty := lty) hprog hmeths htypes)
  go_walk_step (wp_frame_return₁ (ta := ta) (ra := a₂)
    (rcell := ⟨some (.defined ⟨"main.Index"⟩), .int 6 .uint64⟩)
    (tcell := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (tcell' := ⟨some (.defined ⟨"main.Index"⟩), .int 6 .uint64⟩)
    (hstore := fun σ ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 6 = 6 from by decide]))
  go_walk_finish Hcont

/-- **`run`'s body** at 3 voters. -/
theorem wp_run_body_three {ca cba la lba ra : Addr} {cty lty : Option Ty} {k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData threeConfigEntries⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                  .map ⟨some (.base lba)⟩⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData threeAckedEntries⟩ : HeapCell)
      ∗ ra.id ↦ (⟨some (.int .uint64), .int 0 .uint64⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int .uint64), .int 6 .uint64⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec runImpl.body
            [[("$res0", Loc.base ra), ("l", Loc.base la), ("c", Loc.base ca)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hc, Hcb, Hl, Hlb, Hr, Hcont⟩
  rw [runImpl_body_eq]
  go_walk
  unfold runCallSeq
  go_walk
  go_walk_step (wp_init (v := .int 0 .uint64) (hdef := fun σ ht => by
    rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
      (rfl (a := σ.methods))]
    simp [defaultValue, defaultValueFuel, typeResolutionFuel,
      QuorumPin.typeEnv_Index])) as [c3a]
  go_walk 1
  go_walk_step (wp_committedIndexCall_three (ca := ca) (cba := cba) (la := la)
    (lba := lba) (ta := c3a) (cty := cty) (lty := lty) hprog hmeths htypes
    rfl rfl rfl)
  go_walk
  unfold runResSeq
  go_walk
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.int .uint64), .int 0 .uint64⟩)
    (newcell := ⟨some (.int .uint64), .int 6 .uint64⟩)
    (fun σ _ht hlk => by
      have h := storeLoc_int_any (mkind := .uint64) hlk 6
      rw [show IntKind.uint64.normalize 6 = 6 from by decide] at h
      exact h))
  go_walk_finish Hcont

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Iris.GoldenQuorum

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open QuorumPin GoLean.Quorum

/-- **The driver body** — `committedThreeAll`: build `MajorityConfig{1,2,3}`
and `mapAckIndexer{1:12, 2:5, 3:6}` with two `make(map…)`s and three
`m[k] = v` writes each, call `run`, return its answer. -/
theorem wp_threeAll_body {ra : Addr} {k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList) :
    ra.id ↦ (⟨some (.int .uint64), .int 0 .uint64⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int .uint64), .int 6 .uint64⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec threeAllImpl.body [[("$res0", Loc.base ra)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  rw [threeAllImpl_body_eq]
  go_walk
  -- `c := MajorityConfig{1: {}, 2: {}, 3: {}}`
  unfold taCfgSeq
  go_walk
  go_walk_step (wp_init (v := .map ⟨none⟩) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel])) as [c31a, Hc31]
  go_walk
  go_walk_step (wp_make_map (a := c31a)
    (oldcell := ⟨some (.map (.int .uint64) (.defined ⟨"struct{}"⟩)),
                 .map ⟨none⟩⟩)
    (newcell := fun fa => ⟨some (.map (.int .uint64) (.defined ⟨"struct{}"⟩)),
                           .map ⟨some (.base fa)⟩⟩)
    (hstore := fun σ fa _ht hlk => by
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind, typeResolutionFuel])) as [cfgba, Hcfgb, Hc31]
  go_walk
  go_walk_step (wp_eval_strict_nullary_pin (v := .struct ⟨"struct{}"⟩ #[]) rfl
    (fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [applyStrictOp, buildStructValue, buildStructValueFuel,
        buildStructFields, typeResolutionFuel, QuorumPin.typeEnv_structEmpty,
        Functor.map, Except.map, Bind.bind, Except.bind]))
  go_walk_step (wp_stmt_op_apply_store (a := cfgba)
    (oldcell := ⟨none, .mapData #[]⟩)
    (newcell := ⟨none, .mapData
      #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]⟩)
    (happly := fun σ ch ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp +decide [applyStmtOp, valueAsMap, mapEntries, loadLoc, hlk,
        mapEntryIndex?, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_structEmpty,
        normalizeStructValueWith, normalizeFieldsWith,
        checkKeyHashable, valueHashability, coerceStoredValue, storeLoc,
        Functor.map, Except.map, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 1 = 1 from by decide, applyStmtOpCore])) as [Hcfgb]
  go_walk
  go_walk_step (wp_eval_strict_nullary_pin (v := .struct ⟨"struct{}"⟩ #[]) rfl
    (fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [applyStrictOp, buildStructValue, buildStructValueFuel,
        buildStructFields, typeResolutionFuel, QuorumPin.typeEnv_structEmpty,
        Functor.map, Except.map, Bind.bind, Except.bind]))
  go_walk_step (wp_stmt_op_apply_store (a := cfgba)
    (oldcell := ⟨none, .mapData #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]⟩)
    (newcell := ⟨none, .mapData
      #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[]),
        (.int 2 .uint64, .struct ⟨"struct{}"⟩ #[])]⟩)
    (happly := fun σ ch ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp +decide [applyStmtOp, valueAsMap, mapEntries, loadLoc, hlk,
        mapEntryIndex?, valueEq, valueEqFuel, normalizeValueForTy,
        normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_structEmpty, normalizeStructValueWith,
        normalizeFieldsWith, checkKeyHashable, valueHashability,
        coerceStoredValue, storeLoc, Functor.map, Except.map, Bind.bind,
        Except.bind, show IntKind.uint64.normalize 2 = 2 from by decide, applyStmtOpCore])) as [Hcfgb]
  go_walk
  go_walk_step (wp_eval_strict_nullary_pin (v := .struct ⟨"struct{}"⟩ #[]) rfl
    (fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [applyStrictOp, buildStructValue, buildStructValueFuel,
        buildStructFields, typeResolutionFuel, QuorumPin.typeEnv_structEmpty,
        Functor.map, Except.map, Bind.bind, Except.bind]))
  go_walk_step (wp_stmt_op_apply_store (a := cfgba)
    (oldcell := ⟨none, .mapData
      #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[]),
        (.int 2 .uint64, .struct ⟨"struct{}"⟩ #[])]⟩)
    (newcell := ⟨none, .mapData threeConfigEntries⟩)
    (happly := fun σ ch ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp +decide [applyStmtOp, valueAsMap, mapEntries, loadLoc, hlk,
        mapEntryIndex?, valueEq, valueEqFuel, threeConfigEntries,
        normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_structEmpty, normalizeStructValueWith,
        normalizeFieldsWith, checkKeyHashable, valueHashability,
        coerceStoredValue, storeLoc, Functor.map, Except.map, Bind.bind,
        Except.bind, show IntKind.uint64.normalize 3 = 3 from by decide, applyStmtOpCore])) as [Hcfgb]
  -- `l := mapAckIndexer{1: 12, 2: 5, 3: 6}`
  go_walk
  unfold taAckSeq
  go_walk
  go_walk_step (wp_init (v := .map ⟨none⟩) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel])) as [c32a, Hc32]
  go_walk
  go_walk_step (wp_make_map (a := c32a)
    (oldcell := ⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
                 .map ⟨none⟩⟩)
    (newcell := fun fa => ⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
                           .map ⟨some (.base fa)⟩⟩)
    (hstore := fun σ fa _ht hlk => by
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind, typeResolutionFuel])) as [ackba, Hackb, Hc32]
  go_walk
  go_walk_step (wp_stmt_op_apply_store (a := ackba)
    (oldcell := ⟨none, .mapData #[]⟩)
    (newcell := ⟨none, .mapData #[(.int 1 .uint64, .int 12 .uint64)]⟩)
    (happly := fun σ ch ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp [applyStmtOp, valueAsMap, mapEntries, loadLoc, hlk, mapEntryIndex?,
        normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_Index, checkKeyHashable, valueHashability,
        coerceStoredValue, storeLoc, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 1 = 1 from by decide,
        show IntKind.uint64.normalize 12 = 12 from by decide, applyStmtOpCore])) as [Hackb]
  go_walk
  go_walk_step (wp_stmt_op_apply_store (a := ackba)
    (oldcell := ⟨none, .mapData #[(.int 1 .uint64, .int 12 .uint64)]⟩)
    (newcell := ⟨none, .mapData
      #[(.int 1 .uint64, .int 12 .uint64), (.int 2 .uint64, .int 5 .uint64)]⟩)
    (happly := fun σ ch ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp +decide [applyStmtOp, valueAsMap, mapEntries, loadLoc, hlk,
        mapEntryIndex?, valueEq, valueEqFuel, normalizeValueForTy,
        normalizeValueForTyFuel, typeResolutionFuel, QuorumPin.typeEnv_Index,
        checkKeyHashable, valueHashability, coerceStoredValue, storeLoc,
        Bind.bind, Except.bind,
        show IntKind.uint64.normalize 2 = 2 from by decide,
        show IntKind.uint64.normalize 5 = 5 from by decide, applyStmtOpCore])) as [Hackb]
  go_walk
  go_walk_step (wp_stmt_op_apply_store (a := ackba)
    (oldcell := ⟨none, .mapData
      #[(.int 1 .uint64, .int 12 .uint64), (.int 2 .uint64, .int 5 .uint64)]⟩)
    (newcell := ⟨none, .mapData threeAckedEntries⟩)
    (happly := fun σ ch ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp +decide [applyStmtOp, valueAsMap, mapEntries, loadLoc, hlk,
        mapEntryIndex?, valueEq, valueEqFuel, threeAckedEntries,
        normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_Index, checkKeyHashable, valueHashability,
        coerceStoredValue, storeLoc, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 3 = 3 from by decide,
        show IntKind.uint64.normalize 6 = 6 from by decide, applyStmtOpCore])) as [Hackb]
  -- `r := run(c, l)`
  go_walk
  unfold taCallSeq
  go_walk 2
  go_walk_step wp_init_int as [c33a, Hc33]
  go_walk
  go_walk_step (wp_call_enter₂₁ (func := QuorumPin.runImpl)
    (w₀ := .map ⟨some (.base cfgba)⟩)
    (w₁ := .map ⟨some (.base ackba)⟩)
    (dv₀ := .int 0 .uint64)
    (hfind := by rw [hprog]; exact QuorumPin.runImpl_find)
    (hargs := QuorumPin.runImpl_args)
    (hres := QuorumPin.runImpl_results)
    (hnodisp := fun σ hf hm ht => by
      rw [execState_pin_eq (ht.trans htypes) (hf.trans hprog) (hm.trans hmeths)]
      simp +decide [dynamicDispatch?, methodInfoByFuncId?,
        QuorumPin.quorumMethods_eq, Bind.bind, Except.bind])
    (hnorm₀ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_MajorityConfig])
    (hnorm₁ := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_mapAckIndexer])
    (hdef₀ := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
    as [b₀, b₁, b₂]
  go_walk_step (wp_run_body_three (ca := b₀) (cba := cfgba) (la := b₁)
    (lba := ackba) (ra := b₂) hprog hmeths htypes)
  go_walk_step (wp_frame_return_int (ta := c33a) (ra := b₂) (kind := .uint64)
    (tkind := .uint64) (m := 6))
  -- `return r`
  go_walk
  unfold taResSeq
  go_walk
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.int .uint64), .int 0 .uint64⟩)
    (newcell := ⟨some (.int .uint64), .int 6 .uint64⟩)
    (fun σ _ht hlk => by
      have h := storeLoc_int_any (mkind := .uint64) hlk 6
      rw [show IntKind.uint64.normalize 6 = 6 from by decide] at h
      exact h))
  go_walk_finish Hcont

/-- **The `committedThreeAll()` callsite** — the outermost frame. -/
theorem wp_threeAllCall {ta : Addr} {w : GoValue} {env k}
    (hres : LocalEnv.lookup env "$callres" = some (.base ta))
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList) :
    ta.id ↦ (⟨some (.int .uint64), w⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.int .uint64), .int 6 .uint64⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[])
            env k) @ s ; E {{ Φ }} := by
  iintro ⟨Ht, Hcont⟩
  go_walk
  go_walk_step (wp_call_enter_ret1 (func := QuorumPin.threeAllImpl)
    (dv := .int 0 .uint64)
    (hfind := by rw [hprog]; exact QuorumPin.threeAllImpl_find)
    (hargs := QuorumPin.threeAllImpl_args)
    (hres := QuorumPin.threeAllImpl_results)
    (hnodisp := fun σ hm => by
      simp only [dynamicDispatch?, methodInfoByFuncId?, hm.trans hmeths]
      simp +decide [QuorumPin.quorumMethods_eq, Bind.bind, Except.bind])
    (hdef := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel])) as [rra]
  go_walk_step (wp_threeAll_body (ra := rra) hprog hmeths htypes)
  go_walk_step (wp_frame_return_int (ta := ta) (ra := rra) (kind := .uint64)
    (tkind := .uint64) (m := 6))
  go_walk_finish Hcont

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Surface

open GoLean.GoCore GoLean.Quorum

/-! ## 7. THE 3-VOTER TARGET, DISCHARGED

`quorumThreeAllFuncSpec_statement` (`Specs/AutomationTargets.lean`, phase
0 of this arc) is a `def … : Prop` written before the machinery; this is
its discharge. -/

/-- **THE 3-VOTER THEOREM.** `committedThreeAll()` — the pinned lowering
of etcd's own `majority_commit.txt` row — returns `6`, at `GoFuncSpec`
strength: into any caller cell, over any prior value, in any admissible
heap, beside any frame, through the exit pipe (triple + progress).

The per-program obligation is the WP walk `wp_threeAllCall`, whose voter
range goes through `Laws/Range.wp_map_iter_inv` — ONE generic iteration
and a permutation invariant, not the `3! = 6` iteration orders. -/
theorem quorumThreeAllFuncSpec : quorumThreeAllFuncSpec_statement := by
  unfold quorumThreeAllFuncSpec_statement GoFuncSpec
  intro ra w
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths htypes
  simp only [embed]
  iintro ⟨H0, -⟩
  iapply (GoLean.Iris.GoldenQuorum.wp_threeAllCall (ta := ⟨ra⟩) (w := w)
    rfl hprog hmeths htypes)
  isplitl [H0]
  · iexact H0
  iintro H6
  iapply (wp_value' (v := ()))
  iexists (6 : Int)
  isplitl [H6]
  · iexact H6
  · ipureintro
    rfl

/-- **The corollary that names the goal at 3 voters**: the machine's
answer *is* a committed index of `{1,2,3}` under `{1:12, 2:5, 3:6}` —
`GoLean.Quorum.IsCommittedIndex`, the declarative spec of
`deps/raft/quorum/majority.go`, discharged by `isCommittedIndex_threeAll`
(itself the proven general agreement theorem at this instance). Real Go
source → frontend lowering (pinned) → machine walk → declarative quorum
spec, with no unproven link and a genuinely nondeterministic range in the
middle. -/
theorem quorumThreeAllMeetsSpec :
    GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
      quorumLowered.methods ⟨"committedThreeAll"⟩ .uint64 #[] .emp
      (fun n => .pure (0 ≤ n ∧
        GoLean.Quorum.IsCommittedIndex [1, 2, 3] GoLean.Quorum.ackedThreeAll
          n.toNat)) := by
  unfold GoFuncSpec
  intro ra w
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths htypes
  simp only [embed]
  iintro ⟨H0, -⟩
  iapply (GoLean.Iris.GoldenQuorum.wp_threeAllCall (ta := ⟨ra⟩) (w := w)
    rfl hprog hmeths htypes)
  isplitl [H0]
  · iexact H0
  iintro H6
  iapply (wp_value' (v := ()))
  iexists (6 : Int)
  isplitl [H6]
  · iexact H6
  · ipureintro
    exact ⟨by decide, GoLean.Quorum.isCommittedIndex_threeAll⟩

/-! ### The first-order readout, and the negative twin

Both run-CONDITIONED, for the reason recorded once for the whole family
(`quorumOneKnownNotEleven`): a `GoTriple` says nothing about a program
that fails to terminate, so the UNCONDITIONAL `¬ GoFuncSpec` form of
`quorumThreeAllNotTwelve_statement` is not refutable from the triple
alone — it demands EXHIBITING a terminating run. That cost stays
recorded as owed; the honest twin is below. -/

/- `threeOutEnv` moved to `Specs/Statements.lean` (its heap is `quorumOut`,
already there). -/

/-- **The first-order readout**: every terminating run of
`$callres = committedThreeAll()` from the seeded one-cell state leaves
`uint64(6)` at base address 0. -/
theorem quorumThreeAllReturnsSix
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel threeOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 6 .uint64) := by
  have htriple := (quorumThreeAllFuncSpec 0 (.int 0 .uint64)).1
  have hres := htriple quorumOut 1 (heapletOf quorumOut) (∅ : Heaplet)
    { bounded := by
        intro n hn
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rfl
      disj := fun k => .inr (by
        rw [heaplet_get?_eq]
        exact LawfulPartialMap.get?_empty (M := GoHeapF) (k := k))
      cover := fun k c => by
        constructor
        · exact fun h => .inl h
        · rintro (h | h)
          · exact h
          · rw [heaplet_get?_eq,
              LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)] at h
            cases h
      sat_pre := ⟨heapletOf quorumOut, ∅, rfl, rfl,
        fun k => .inr (by
          rw [heaplet_get?_eq]
          exact LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)),
        fun k c => ⟨fun h => .inl h, fun h => h.elim id (fun h0 => by
          rw [heaplet_get?_eq,
            LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)] at h0
          cases h0)⟩⟩
      wf := by decide +kernel }
    fuel ch σf ch' hrun
  obtain ⟨h, _hd, hsub, _hF, hsat⟩ := hres
  obtain ⟨n, h₁, h₂, hp1, hp2, _hdisj, hcov⟩ := hsat
  obtain ⟨hn6, rfl⟩ := hp2
  subst hn6
  have hget : h.get? 0 = some ⟨some (.int .uint64), .int 6 .uint64⟩ := by
    rw [hcov]
    exact Or.inl (by rw [hp1]; exact heaplet_get?_insert_self)
  have := hsub 0 ⟨some (.int .uint64), .int 6 .uint64⟩ hget
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at this
  exact loadLoc_base_of_lookup this

/-- **The negative twin** — no terminating run leaves `12`, the LARGEST
acked index (the answer a "returns something a voter acked" bug would
give, and the value `quorumThreeAllNotTwelve_statement` names). -/
theorem quorumThreeAllNotTwelve
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel threeOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"committedThreeAll"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) ≠ .ok (.int 12 .uint64) := by
  intro h12
  have h6 := quorumThreeAllReturnsSix fuel ch σf ch' hrun
  have := h6.symm.trans h12
  injection this with hval
  injection hval with hn _
  exact absurd hn (by decide)

end GoLean.Surface
