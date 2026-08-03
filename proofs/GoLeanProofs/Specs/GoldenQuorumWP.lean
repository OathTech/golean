import GoLeanProofs.SurfaceExit
import GoLeanProofs.Laws.Control
import GoLeanProofs.Laws.Init
import GoLeanProofs.Laws.StmtOps
import GoLeanProofs.Specs.GoldenQuorumPin
import GoLeanProofs.Laws.Unwind
import GoLeanProofs.Specs.QuorumRefSpec
import GoLeanProofs.Specs.Statements
import GoLeanProofs.Tactics.GoWalk

/-!
# The quorum walk — the FIRST machine discharge, and the math link
(quorum pilot phase 4, 2026-07-31)

Honest status, stated once and not softened anywhere below:

- **PROVEN, THE ARC'S NAMED GOAL (2026-07-31, the summit slice)**:
  `quorumOneKnownFuncSpec` — the pinned lowering of the REAL etcd-io/raft
  quorum driver, `committedOneKnown()`, returns `12` at `GoFuncSpec`
  strength; and `quorumOneKnownMeetsSpec` restates that with the
  DECLARATIVE quorum spec as the postcondition (`IsCommittedIndex [1]
  ackedOneKnown`). The walk goes through the real `run`,
  `main.MajorityConfig.CommittedIndex` and `main.mapAckIndexer.AckedIndex`
  — two `make(map…)`s that allocate inside the apply step, a map length
  read, the on-stack `[7]uint64` scratch array and its reslice, the
  nondeterministic map range, interface dispatch, comma-ok, a store
  through a slice index, `slices.Sort`, and the `n - (n/2+1)` readout.
  **Scope: n = 1** — the range's nondeterminism is degenerate and the
  fit test takes the reslice branch; the three-voter widening is
  recorded in the arc doc.
- **PROVEN, machine-level**: `quorumAckedIndexFuncSpec2` — the real
  `main.mapAckIndexer.AckedIndex` of the PINNED lowering, at
  `GoFuncSpec2` strength (the multi-result surface judgment), called on a
  concrete one-entry `mapAckIndexer`: the caller's two cells receive
  `(12, true)`. This is the first `GoFuncSpec2` discharge — the W1 arity
  widening's first instance — and it walks real Go machinery end to end:
  a two-target/two-argument call, a frame entry that allocates four cells
  at named types, a comma-ok map read, two writes at a defined type, and
  a TWO-result frame exit.
- **PROVEN, pure math**: the value the full `CommittedIndex` walk must
  land on, and its upgrade to the declarative spec.
- **NOT PROVEN, and recorded as such**: the
  `quorumOneKnownNotEleven_statement` target (written in phase 4,
  `39891ae` — see the provenance note on the def) — the UNCONDITIONAL
  `¬ GoFuncSpec … (n = 11)`. It is not refutable from the triple: a
  `GoTriple` is vacuously true of a program that fails to terminate, so
  refuting it demands EXHIBITING a terminating run (a kernel evaluation
  of the interpreter over the whole pinned program). The run-conditioned
  twin `quorumOneKnownNotEleven` — the golden precedent's shape
  (`goldenNotThree`) — is proven below instead.

The claim shape, for the record: the machine result `12` equals
`GoLean.Quorum.committedIndexRef [1] (fun v => if v = 1 then some 12
else none)` (proven by `rfl` below), and `committedIndexRef_meets_spec`
(PROVEN, `Specs/QuorumRefSpec.lean`) upgrades that to
`IsCommittedIndex` — so the ONLY missing link between the pinned real
etcd-io/raft lowering and the declarative quorum spec is the machine
walk. That is the point of stating the targets here rather than in chat.
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine
open GoLean.Iris GoLean.Iris.GoldenQuorum

set_option linter.unusedSimpArgs false

namespace GoLean.Quorum

/-! ## The math half — PROVEN

These are theorems, not targets. They pin the value the machine walk must
land on and immediately upgrade it to the declarative spec. -/

-- `ackedOneKnown` moved to `Specs/Statements.lean` — the Iris-free
-- statement layer (comparator-judge sprint, 2026-08-02).

/-- **The value the machine must produce**, from the reference — `rfl`,
so it is a computation, not a claim. -/
theorem committedIndexRef_oneKnown :
    committedIndexRef [1] ackedOneKnown = 12 := rfl

/-- **The declarative spec holds at 12** for this instance: committedness
and maximality, via the proven general agreement theorem. Together with a
machine walk landing on `12`, this is the tier-1 statement on a one-voter
config. -/
theorem isCommittedIndex_oneKnown : IsCommittedIndex [1] ackedOneKnown 12 :=
  committedIndexRef_oneKnown ▸ committedIndexRef_meets_spec [1] ackedOneKnown
    (by decide)

/-- Negative twin: `11` is NOT the committed index of this instance
(maximality fails at 12) — the guard against a spec that accepts anything
below the true value. -/
theorem not_isCommittedIndex_oneKnown_11 :
    ¬ IsCommittedIndex [1] ackedOneKnown 11 := by
  rintro (⟨h, -⟩ | ⟨-, -, hmax⟩)
  · simp at h
  · exact absurd (hmax 12 (by omega)) (by decide)

end GoLean.Quorum


namespace GoLean.Iris.GoldenQuorum

/-! ## The `AckedIndex` machine walk (quorum pilot phase 4, slice 5)

The real `main.mapAckIndexer.AckedIndex` of the pinned lowering, walked
end to end: the callsite's two targets and two arguments, the frame
entry, the body (two declarations at named types, the comma-ok read, the
two result writes, `return`), and the two-result frame exit. Every step
is one of the general laws; the only quorum-specific inputs are the pin
projections (`QuorumPin.*`, all `rfl`) and the concrete map. -/

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- **The `AckedIndex` body walk** on an arbitrary receiver map, under the
frame environment frame entry produces. Declares `idx : main.Index` and
`ok : bool` (the named-type declaration is what needs `wp_init`'s
type-environment pin), performs the comma-ok read
(`wp_map_lookup_ackedIndex_entries`, the general law on the REAL
statement), writes both results and returns. The parameter and map cells
are dropped affinely at the end; the two RESULT cells are handed to the
continuation holding the looked-up index and `true`.

**Generalized 2026-08-01 (proof-automation arc, phases 3 and 4)** from the
one-entry receiver `{q ↦ v}` to an ARBITRARY entry array plus `hpair`,
the lookup's answer, and then from a FOUND key to the comma-ok pair
`(v, b)` at an arbitrary `b`: a voter with no entry is Go's "has not
reported yet", and the `∀`-config walk takes that iteration too. The one-entry receiver was an artefact of the n = 1
walk, not of Go: at any config with more than one voter the same method
body is walked against a multi-entry `AckedIndexer`. The one-entry form
survives verbatim as `wp_ackedIndex_body` below, derived from this. -/
theorem wp_ackedIndex_body_entries {ma ida mba ra₀ ra₁ : Addr} {mty : Option Ty}
    {entries : Array (GoValue × GoValue)} {q v : Int} {b : Bool} {k}
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hq : IntKind.uint64.normalize q = q)
    (hv : IntKind.uint64.normalize v = v)
    (hpair : ∀ σ : ExecState, σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base mba) = some ⟨mty, .mapData entries⟩ →
      mapLookupValue σ ⟨some (.base mba)⟩ (.int q .uint64) (.int .uint64)
          (.defined ⟨"main.Index"⟩)
        = .ok (.int v .uint64, b)) :
    ma.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
              .map ⟨some (.base mba)⟩⟩ : HeapCell)
      ∗ ida.id ↦ (⟨some (.int .uint64), .int q .uint64⟩ : HeapCell)
      ∗ mba.id ↦ (⟨mty, .mapData entries⟩ : HeapCell)
      ∗ ra₀.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ ra₁.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (mba.id ↦ (⟨mty, .mapData entries⟩ : HeapCell)
          ∗ ra₀.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int v .uint64⟩ : HeapCell)
          ∗ ra₁.id ↦ (⟨some .bool, .bool b⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec QuorumPin.ackedIndexImpl.body
            [[("$res1", Loc.base ra₁), ("$res0", Loc.base ra₀),
              ("id", Loc.base ida), ("m", Loc.base ma)]] k) @ s ; E {{ Φ }} := by
  iintro ⟨Hm, Hid, Hmb, Hr0, Hr1, Hcont⟩
  rw [QuorumPin.ackedIndexImpl_body_eq]
  go_walk
  -- `var idx main.Index` — the NAMED-type default needs the `σ.types` pin
  go_walk_step (wp_init (v := .int 0 .uint64) (hdef := fun σ ht => by
    rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
      (rfl (a := σ.methods))]
    simp [defaultValue, defaultValueFuel, typeResolutionFuel,
      QuorumPin.typeEnv_Index]))
  go_walk
  -- `var ok bool`
  go_walk_step (wp_init (v := .bool false) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  go_walk
  -- the comma-ok map read. The walk stops in front of it at the REGISTERED
  -- one-entry law's resource boundary (its `{q ↦ v}` data cell cannot be
  -- framed against this theorem's arbitrary `entries`), which is exactly
  -- where the general law is handed over.
  go_walk_step (wp_map_lookup_ackedIndex_entries (mba := mba) (mty := mty)
    (entries := entries) (q := q) (v := v) (b := b) htypes hq hv hpair
    rfl rfl rfl rfl)
  go_walk
  -- `$res0 = idx` — a store at the DEFINED type `main.Index`
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (newcell := ⟨some (.defined ⟨"main.Index"⟩), .int v .uint64⟩)
    (fun σ ht hl => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hl ⊢
      simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, hv, Bind.bind,
        Except.bind]))
  go_walk
  -- `$res1 = ok`
  go_walk_step (wp_assign_store (oldcell := ⟨some .bool, .bool false⟩)
    (newcell := ⟨some .bool, .bool b⟩)
    (fun σ _ht hl => by
      simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind, typeResolutionFuel]))
  go_walk_finish Hcont

/-- **The one-entry instance**, the n = 1 summit's `AckedIndex` body walk,
unchanged in statement: receiver map `{q ↦ v}`, the key present. Derived
from the general form above by `mapLookupValue_singleton`. -/
theorem wp_ackedIndex_body {ma ida mba ra₀ ra₁ : Addr} {mty : Option Ty}
    {q v : Int} {k}
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hq : IntKind.uint64.normalize q = q)
    (hv : IntKind.uint64.normalize v = v) :
    ma.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
              .map ⟨some (.base mba)⟩⟩ : HeapCell)
      ∗ ida.id ↦ (⟨some (.int .uint64), .int q .uint64⟩ : HeapCell)
      ∗ mba.id ↦ (⟨mty, .mapData #[(.int q .uint64, .int v .uint64)]⟩ : HeapCell)
      ∗ ra₀.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ ra₁.id ↦ (⟨some .bool, .bool false⟩ : HeapCell)
      ∗ (ra₀.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int v .uint64⟩ : HeapCell)
          ∗ ra₁.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec QuorumPin.ackedIndexImpl.body
            [[("$res1", Loc.base ra₁), ("$res0", Loc.base ra₀),
              ("id", Loc.base ida), ("m", Loc.base ma)]] k) @ s ; E {{ Φ }} :=
  by
  iintro ⟨Hm, Hid, Hmb, Hr0, Hr1, Hcont⟩
  iapply (wp_ackedIndex_body_entries (mba := mba) (mty := mty)
    (entries := #[(.int q .uint64, .int v .uint64)]) (q := q) (v := v)
    htypes hq hv (fun σ _ht hl => mapLookupValue_singleton σ hl))
  iframe
  -- the receiver's DATA cell rides back out of the general law and is dropped
  -- here, which is what keeps the one-entry statement unchanged
  iintro ⟨-, Hr0', Hr1'⟩
  iapply Hcont $$ [$Hr0' $Hr1']

/-- **The `AckedIndex` call walk**, end to end: two target addresses, the
receiver and the index argument, the STATIC frame entry
(`wp_call_enter_ackedIndexImpl`), the body, and the TWO-result frame exit
(`wp_frame_return₂`) that writes `12` and `true` into the caller's cells.
Generic in the caller's environment, target cells and their prior values;
the map is the concrete `{3 ↦ 12}` receiver. -/
theorem wp_ackedIndexCall {ma mba ta tb : Addr} {mty : Option Ty} {q v : Int}
    {w₁ w₂ : GoValue} {env k}
    (hres0 : LocalEnv.lookup env "$callres0" = some (Loc.base ta))
    (hres1 : LocalEnv.lookup env "$callres1" = some (Loc.base tb))
    (hm : LocalEnv.lookup env "m" = some (Loc.base ma))
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hq : IntKind.uint64.normalize q = q)
    (hv : IntKind.uint64.normalize v = v) :
    ma.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
              .map ⟨some (.base mba)⟩⟩ : HeapCell)
      ∗ mba.id ↦ (⟨mty, .mapData #[(.int q .uint64, .int v .uint64)]⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.int .uint64), w₁⟩ : HeapCell)
      ∗ tb.id ↦ (⟨some .bool, w₂⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.int .uint64), .int v .uint64⟩ : HeapCell)
          ∗ tb.id ↦ (⟨some .bool, .bool true⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec
            (.call #[.var "$callres0", .var "$callres1"]
              ⟨"main.mapAckIndexer.AckedIndex"⟩
              #[.var "m", .intLit q .uint64]) env k) @ s ; E {{ Φ }} := by
  iintro ⟨Hm, Hmb, Ht, Htb, Hcont⟩
  -- the targets, the two arguments and the STATIC frame entry
  -- (`wp_call_enter_ackedIndexImpl`, a registered law: its premises are the
  -- three ghost pins, which are hypotheses here)
  go_walk with [hq]
  -- the body
  go_walk_step (wp_ackedIndex_body (mty := mty) (q := q) (v := v)
    htypes hq hv) with [hq]
  -- the TWO-result frame exit
  go_walk_step (wp_frame_return₂
    (rcell₀ := ⟨some (.defined ⟨"main.Index"⟩), .int v .uint64⟩)
    (rcell₁ := ⟨some .bool, .bool true⟩)
    (tcell₀ := ⟨some (.int .uint64), w₁⟩)
    (tcell₀' := ⟨some (.int .uint64), .int v .uint64⟩)
    (tcell₁ := ⟨some .bool, w₂⟩)
    (tcell₁' := ⟨some .bool, .bool true⟩)
    (hstore₀ := fun σ _ht hl => by
      have h := storeLoc_int_any (mkind := .uint64) hl v
      rw [hv] at h
      exact h)
    (hstore₁ := fun σ _ht hl => by
      simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind, typeResolutionFuel]))
  go_walk_finish Hcont

end


/-! ## THE SUMMIT WALK: `main.MajorityConfig.CommittedIndex` at n = 1
(quorum pilot phase 4, the summit slice)

The real etcd-io/raft `CommittedIndex`, walked over the PINNED lowering on
a one-voter config. Each theorem below covers one statement (or one
statement group) of the body and is generic in the surrounding
environment, the continuation and the addresses; the composition
`wp_committedIndex_body` chains them. -/

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

open QuorumPin

/-- `n := len(c)` — the declaration, the map-length read (a state-READING
strict op on the config's data cell) and the store. Generic in the config
map's contents: `n` is its entry count. -/
theorem wp_ci_len {ca cba : Addr} {cty : Option Ty}
    {entries : Array (GoValue × GoValue)} {rest env k}
    (hsize : IntKind.int.normalize (Int.ofNat entries.size)
      = Int.ofNat entries.size)
    (hc : LocalEnv.lookup env "c" = some (.base ca)) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData entries⟩ : HeapCell)
      ∗ iprop(∀ na : Addr,
          ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
                    .map ⟨some (.base cba)⟩⟩ : HeapCell)
            ∗ cba.id ↦ (⟨cty, .mapData entries⟩ : HeapCell)
            ∗ na.id ↦ (⟨some (.int .int),
                        .int (Int.ofNat entries.size) .int⟩ : HeapCell) -∗
          WP (Config.next (.seq rest (env.declare "n" (.base na)) k))
            @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciLenStmt env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hc, Hcb, Hcont⟩
  rw [ciLenStmt_eq]
  go_walk
  -- `len(c)` — a state-READING strict op on the config's data cell
  go_walk_step (wp_strict_apply_read (a := cba) (cell := ⟨cty, .mapData entries⟩)
    (out := .int (Int.ofNat entries.size) .int)
    (happly := fun σ _ht hl => by
      simp [applyStrictOp, loadLoc, hl, Bind.bind, Except.bind]))
  -- the store into `n`
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int (Int.ofNat entries.size) .int⟩)
    (fun σ _ht hl => by
      have h := storeLoc_int_any (mkind := .int) hl (Int.ofNat entries.size)
      rw [hsize] at h
      simpa using h))
  go_walk_finish Hcont

/-- `if n == 0 { return math.MaxUint64 }` — the empty-config early
return, on the NOT-taken branch. Generic in `n`; the premise is the
machine's own comparison, which at any nonzero `n` is `false`. -/
theorem wp_ci_emptyIf {na : Addr} {n : Int} {rest env k}
    (hn : LocalEnv.lookup env "n" = some (.base na))
    (hcmp : ∀ σ : ExecState,
      applyStrictOp σ (.eqCmp (.int .int)) [.int n .int, .int 0 .int]
        = .ok (.bool false, σ)) :
    na.id ↦ (⟨some (.int .int), .int n .int⟩ : HeapCell)
      ∗ (na.id ↦ (⟨some (.int .int), .int n .int⟩ : HeapCell) -∗
          WP (Config.next (.seq rest env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciEmptyIf env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hn, Hcont⟩
  rw [ciEmptyIf_eq]
  go_walk_finish Hcont

/-- `var stk [7]uint64` — the on-stack scratch declaration. Zero
premises: the array default is state-independent. -/
theorem wp_ci_stkDecl {rest env k} :
    iprop(∀ sta : Addr, sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkZero⟩ : HeapCell) -∗
        WP (Config.next (.seq rest (env.declare "stk" (.base sta)) k))
          @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciStkDecl env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro Hcont
  rw [ciStkDecl_eq]
  go_walk
  go_walk_step (wp_init (v := stkZero) (hdef := fun σ _ => defaultValue_stk σ))
  go_walk_finish Hcont

/-- `var srt []uint64` — the result slice declaration (nil slice). -/
theorem wp_ci_srtDecl {rest env k} :
    iprop(∀ sra : Addr,
        sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨none, 0, 0, 0⟩⟩ : HeapCell) -∗
        WP (Config.next (.seq rest (env.declare "srt" (.base sra)) k))
          @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciSrtDecl env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro Hcont
  rw [ciSrtDecl_eq]
  go_walk
  go_walk_step (wp_init (v := .slice ⟨none, 0, 0, 0⟩) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel]))
  go_walk_finish Hcont

/-- `if len(stk) >= n { srt = stk[:n] }` at `n = 1` — the TAKEN branch:
the on-stack array is resliced, so no allocation happens (the
`make([]uint64, n)` else-branch is the widening's other side). `stk[:n]`
is a state-READING strict op: it loads the array to learn its size, which
becomes the resulting slice's capacity (7). -/
theorem wp_ci_fitIf_one {na sta sra : Addr} {w : GoValue} {rest env k}
    (hn : LocalEnv.lookup env "n" = some (.base na))
    (hstk : LocalEnv.lookup env "stk" = some (.base sta))
    (hsrt : LocalEnv.lookup env "srt" = some (.base sra)) :
    na.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell)
      ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkZero⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)), w⟩ : HeapCell)
      ∗ (na.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell)
          ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkZero⟩ : HeapCell)
          ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                       .slice ⟨some (.base sta), 0, 1, 7⟩⟩ : HeapCell)
          -∗ WP (Config.next (.seq rest env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciFitIf env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hn, Hstk, Hsrt, Hcont⟩
  rw [ciFitIf_eq]
  go_walk
  -- `stk[:n]` — a state-READING strict op: the array is loaded to learn its
  -- size, which becomes the resulting slice's capacity
  go_walk_step (wp_strict_apply_read (a := sta)
    (cell := ⟨some (.array 7 (.int .uint64)), stkZero⟩)
    (out := .slice ⟨some (.base sta), 0, 1, 7⟩)
    (happly := fun σ _ht hl => by
      simp [applyStrictOp, applySlice, loadLoc, hl, stkZero, valueAsInt,
        sliceFromArray, checkSliceBounds, Bind.bind, Except.bind]))
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.slice (.int .uint64)), w⟩)
    (newcell := ⟨some (.slice (.int .uint64)),
                 .slice ⟨some (.base sta), 0, 1, 7⟩⟩)
    (fun σ _ht hl => by
      simp [storeLoc, hl, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind, typeResolutionFuel]))
  go_walk_finish Hcont

/-- **The voter loop's BODY, one iteration** — `if idx, ok :=
l.AckedIndex(id); ok { srt[i] = uint64(idx); i-- }` under the range's
per-iteration scope, with the key cell `pa` holding voter `1`.

EXTRACTED from `wp_ci_loop_one` (proof-automation arc phase 1,
2026-08-01), tactic text unchanged except for the three `"i"` lookups,
which now resolve through the `hi` hypothesis instead of a syntactically
present `declare` layer (the environment is a variable here). The
extraction is what lets the loop's range segment be discharged by the
INDUCTIVE range rule `wp_map_iter_inv` — the body obligation that rule
asks for is exactly this statement — instead of a bare
`wp_map_iter_next_key` + hand-enumerated pick.

The walk itself is the arc's semantic centre: the real INTERFACE dispatch
through the `main.AckedIndexer.AckedIndex` anchor into
`main.mapAckIndexer.AckedIndex`, the comma-ok read inside it, the
two-result frame exit, and the store THROUGH A SLICE INDEX into the
on-stack backing array. -/
theorem wp_ci_range_body_one {ia la lba sra sta pa : Addr}
    {lty : Option Ty} {env k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hl : LocalEnv.lookup env "l" = some (.base la))
    (hsrt : LocalEnv.lookup env "srt" = some (.base sra))
    (hi : LocalEnv.lookup env "i" = some (.base ia)) :
    pa.id ↦ (⟨some (.int .uint64), .int 1 .uint64⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData
          #[(.int 1 .uint64, .int 12 .uint64)]⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, 1, 7⟩⟩ : HeapCell)
      ∗ ia.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkZero⟩ : HeapCell)
      ∗ (la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
          ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, 1, 7⟩⟩ : HeapCell)
          ∗ ia.id ↦ (⟨some (.int .int), .int (-1) .int⟩ : HeapCell)
          ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkOne 12⟩ : HeapCell)
          -∗ WP (Config.next (.mapIterK (some "id") none (.int .uint64)
                  (.defined ⟨"struct{}"⟩) rangeBody #[] env k))
              @ s ; E {{ Φ }})
      ⊢ WP (Config.exec rangeBody (env.pushScope.declare "id" (.base pa))
            (.mapIterK (some "id") none (.int .uint64)
              (.defined ⟨"struct{}"⟩) rangeBody #[] env k)) @ s ; E {{ Φ }} := by
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
  go_walk
  go_walk_step (wp_ackedIndex_body (mty := lty) (q := 1) (v := 12) htypes
    (by decide) (by decide))
  go_walk_step (wp_frame_return₂
    (rcell₀ := ⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩)
    (rcell₁ := ⟨some .bool, .bool true⟩)
    (tcell₀ := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (tcell₀' := ⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩)
    (tcell₁ := ⟨some .bool, .bool false⟩)
    (tcell₁' := ⟨some .bool, .bool true⟩)
    (hstore₀ := fun σ ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 12 = 12 from by decide])
    (hstore₁ := fun σ _ht hlk => by
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind, typeResolutionFuel]))
  -- `if ok { srt[i] = uint64(idx); i-- }`
  go_walk
  unfold ciOkIf
  go_walk
  unfold ciOkThen
  go_walk
  -- the store THROUGH A SLICE INDEX into the on-stack backing array
  go_walk_step (wp_assign_store_loc (a := sta)
    (oldcell := ⟨some (.array 7 (.int .uint64)), stkZero⟩)
    (newcell := ⟨some (.array 7 (.int .uint64)), stkOne 12⟩)
    (fun σ _ht hlk => by
      simp [storeLoc, loadLoc, hlk, stkZero, stkOne, arrayIndexNat, arraySet,
        coerceStoredValue, normalizeValueForTy, normalizeValueForTyFuel,
        normalizeListWith, Bind.bind, Except.bind, Functor.map, Except.map,
        show IntKind.uint64.normalize 12 = 12 from by decide,
        show IntKind.uint64.normalize 0 = 0 from by decide, typeResolutionFuel]))
  -- `i--`
  go_walk
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int (-1) .int⟩)
    (fun σ _ht hlk => by
      have h := storeLoc_int_any (mkind := .int) hlk (-1)
      rw [show IntKind.int.normalize (-1) = -1 from by decide] at h
      exact h))
  -- unwind the two pushed scopes of the `if` body and the two of the range body
  go_walk_finish Hk

/-- **The voter loop at ONE entry** — `for id := range c { if idx, ok :=
l.AckedIndex(id); ok { srt[i] = uint64(idx); i-- } }`. This is the walk's
semantic centre: the nondeterministic map range (degenerate at one
entry — the choice quantifier is discharged by `i < 1`), the real
INTERFACE dispatch through the `main.AckedIndexer.AckedIndex` anchor into
`main.mapAckIndexer.AckedIndex`, the comma-ok read inside it, the
two-result frame exit, and the store THROUGH A SLICE INDEX into the
on-stack backing array. -/
theorem wp_ci_loop_one {na ca cba la lba sra sta : Addr}
    {cty lty : Option Ty} {rest env k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hn : LocalEnv.lookup env "n" = some (.base na))
    (hc : LocalEnv.lookup env "c" = some (.base ca))
    (hl : LocalEnv.lookup env "l" = some (.base la))
    (hsrt : LocalEnv.lookup env "srt" = some (.base sra)) :
    na.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell)
      ∗ ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
                  .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData
          #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData
          #[(.int 1 .uint64, .int 12 .uint64)]⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, 1, 7⟩⟩ : HeapCell)
      ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkZero⟩ : HeapCell)
      ∗ (na.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell)
          ∗ ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
                      .map ⟨some (.base cba)⟩⟩ : HeapCell)
          ∗ cba.id ↦ (⟨cty, .mapData
              #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]⟩ : HeapCell)
          ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                      .interface (.defined ⟨"main.mapAckIndexer"⟩)
                        (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
          ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                       .slice ⟨some (.base sta), 0, 1, 7⟩⟩ : HeapCell)
          ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkOne 12⟩ : HeapCell)
          -∗ WP (Config.next (.seq rest env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec ciLoopBlock env (.seq rest env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hn, Hc, Hcb, Hl, Hlb, Hsr, Hst, Hcont⟩
  rw [ciLoopBlock_eq]
  go_walk
  unfold ciIDecl
  go_walk 2
  -- `var i int` — named, because the range's INVARIANT below has to mention
  -- the cell this declaration allocates
  go_walk_step wp_init_int as [ia]
  go_walk
  -- `i = n - 1`
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int 0 .int⟩)
    (fun σ _ht hl' => by
      have h := storeLoc_int_any (mkind := .int) hl' 0
      rw [show IntKind.int.normalize 0 = 0 from by decide] at h
      exact h))
  -- the range itself: dispatch, read the map cell, take the snapshot
  rw [rangeStmt_eq]
  go_walk
  go_walk_step (wp_map_range_snapshot (ba := cba) (mty := cty)
    (entries := #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]))
  -- THE RANGE, through the INDUCTIVE RANGE RULE (`Laws/Range`,
  -- `wp_map_iter_inv`): one generic-iteration obligation
  -- (`wp_ci_range_body_one`) and an invariant over the REMAINING
  -- snapshot, instead of the hand-enumerated pick this walk used before
  -- (proof-automation arc phase 1, 2026-08-01). The invariant is the
  -- honest reachable set at n = 1: before any iteration the snapshot is
  -- the one-entry config and the scratch array is zeroed; after it the
  -- snapshot is empty, `srt[0]` holds `12` and `i` has been decremented.
  -- `n`, `c` and the config's data cell are untouched by the body, so
  -- they stay in the ambient context rather than in the invariant.
  iapply (wp_map_iter_inv
    (I := fun rem =>
      if rem.size = 0 then
        iprop(la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
          ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, 1, 7⟩⟩ : HeapCell)
          ∗ ia.id ↦ (⟨some (.int .int), .int (-1) .int⟩ : HeapCell)
          ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkOne 12⟩ : HeapCell))
      else
        iprop(⌜rem = #[((GoValue.int 1 .uint64),
                        (GoValue.struct ⟨"struct{}"⟩ #[]))]⌝
          ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
          ∗ lba.id ↦ (⟨lty, .mapData
              #[(.int 1 .uint64, .int 12 .uint64)]⟩ : HeapCell)
          ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, 1, 7⟩⟩ : HeapCell)
          ∗ ia.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
          ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkZero⟩ : HeapCell)))
    (hnorm := fun σ _htypes p hp => by
      obtain rfl : p = ((GoValue.int 1 .uint64),
          (GoValue.struct ⟨"struct{}"⟩ #[])) := by simpa using hp
      simp [normalizeValueForTy, normalizeValueForTyFuel,
        show IntKind.uint64.normalize 1 = 1 from by decide, typeResolutionFuel])
    (Hbody := by
      intro rem i hidx pa
      rw [if_neg (by omega : ¬ rem.size = 0)]
      iintro ⟨⟨%hrem, Hl, Hlb, Hsr, Hi, Hst⟩, Hid, Hk⟩
      subst hrem
      obtain rfl : i = 0 := Nat.lt_one_iff.mp (by simpa using hidx)
      have herase : (#[((GoValue.int 1 .uint64),
            (GoValue.struct ⟨"struct{}"⟩ #[]))] : Array (GoValue × GoValue)).eraseIdx
              0 hidx = #[] := by
        simp
      simp only [herase, List.getElem_toArray, List.getElem_cons_zero,
        Array.size_empty, reduceIte]
      iapply (wp_ci_range_body_one (ia := ia) (la := la) (lba := lba)
        (sra := sra) (sta := sta) (pa := pa) (lty := lty) hprog hmeths htypes
        (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
          Scope.lookup, hl])
        (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
          Scope.lookup, hsrt])
        (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
          Scope.lookup]))
      -- every premise, the continuation wand included, is in the context
      iframe))
  rw [if_neg (by decide : ¬ (#[((GoValue.int 1 .uint64),
      (GoValue.struct ⟨"struct{}"⟩ #[]))] : Array (GoValue × GoValue)).size = 0)]
  -- the invariant at ENTRY: the reachable-snapshot fact, then the cells (by
  -- framing — `go_walk` has renamed them, and the entailment does not care)
  iframe
  isplitl []
  · ipureintro
    rfl
  · rw [if_pos (by decide : (#[] : Array (GoValue × GoValue)).size = 0)]
    iintro ⟨Hl, Hsr, Hi, Hst⟩
    go_walk_finish Hcont

/-- **The tail** — `slices.Sort(srt)`, `pos := n - (n/2+1)`,
`return Index(srt[pos])`. At `n = 1` the sort is over a one-element
window (so the backing array is unchanged, but the machine still performs
the write-back), `pos` is `1 - (0 + 1) = 0`, and `srt[0]` is the acked
index — Go's `n/2+1`-th largest, read out of the on-stack array. -/
theorem wp_ci_tail_one {na sra sta ra : Addr} {env k}
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hn : LocalEnv.lookup env "n" = some (.base na))
    (hsrt : LocalEnv.lookup env "srt" = some (.base sra))
    (hres : LocalEnv.lookup env "$res0" = some (.base ra)) :
    na.id ↦ (⟨some (.int .int), .int 1 .int⟩ : HeapCell)
      ∗ sra.id ↦ (⟨some (.slice (.int .uint64)),
                   .slice ⟨some (.base sta), 0, 1, 7⟩⟩ : HeapCell)
      ∗ sta.id ↦ (⟨some (.array 7 (.int .uint64)), stkOne 12⟩ : HeapCell)
      ∗ ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec sortStmt env
            (.seq [ciPosStmt, ciResStmt] env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hn, Hsr, Hst, Hr, Hcont⟩
  -- `slices.Sort(srt)` — at n = 1 the window is one element, but the machine
  -- still performs the sort
  rw [sortStmt_eq]
  go_walk
  go_walk_step (wp_sort_slice (a := sta)
    (oldcell := ⟨some (.array 7 (.int .uint64)), stkOne 12⟩)
    (newcell := ⟨some (.array 7 (.int .uint64)), stkOne 12⟩)
    (happly := by
      intro σ ch _ht hlk
      simp [applyStmtOp, valueAsSlice, validateSlice, sliceIndexLoc, loadLoc,
        hlk, stkOne, heap_lookup_set_base_self, Bind.bind, Except.bind,
        List.range', List.forIn_cons, List.forIn_nil, arrayGet, arrayIndexNat,
        storeLoc, arraySet, coerceStoredValue, normalizeValueForTy,
        normalizeValueForTyFuel, normalizeListWith, sortLe, insertLe,
        heap_set_set_of_lookup hlk, Functor.map, Except.map,
        show IntKind.uint64.normalize 12 = 12 from by decide,
        show IntKind.uint64.normalize 0 = 0 from by decide, typeResolutionFuel]))
  -- `pos := n - (n/2 + 1)` — pure integer arithmetic throughout
  go_walk
  rw [ciPosStmt_eq]
  go_walk
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.int .int), .int 0 .int⟩)
    (newcell := ⟨some (.int .int), .int 0 .int⟩)
    (fun σ _ht hlk => by
      have h := storeLoc_int_any (mkind := .int) hlk 0
      rw [show IntKind.int.normalize 0 = 0 from by decide] at h
      exact h))
  -- `return Index(srt[pos])`
  go_walk
  rw [ciResStmt_eq]
  go_walk
  go_walk_step (wp_strict_apply_read (a := sta)
    (cell := ⟨some (.array 7 (.int .uint64)), stkOne 12⟩)
    (out := .int 12 .uint64)
    (happly := fun σ _ht hlk => by
      simp [applyStrictOp, valueAsInt, sliceIndexLoc, validateSlice, loadLoc,
        hlk, stkOne, arrayGet, arrayIndexNat, Bind.bind, Except.bind]))
  go_walk_step (wp_strict_apply_pin (out := .int 12 .uint64)
    (happly := fun σ ht => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))]
      simp [applyStrictOp, convertValueToTy, convertValueToTyFuel,
        typeResolutionFuel, resolveDefinedAliases, resolveDefinedAliasesFuel,
        QuorumPin.typeEnv_Index, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 12 = 12 from by decide]))
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (newcell := ⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩)
    (fun σ ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 12 = 12 from by decide]))
  go_walk_finish Hcont

/-- **THE `CommittedIndex` BODY WALK** — the real
`main.MajorityConfig.CommittedIndex` of the pinned etcd-io/raft lowering,
executed end to end on the one-voter instance `MajorityConfig{1:{}}` with
`mapAckIndexer{1:12}`, under the frame environment frame entry produces.
Every statement of `majority.go`'s algorithm is walked: `n := len(c)`,
the empty-config early return (not taken), the on-stack `[7]uint64`
scratch array, the `len(stk) >= n` reslice, the voter range with its
interface dispatch and comma-ok, `slices.Sort`, `pos := n - (n/2+1)` and
the `Index(srt[pos])` readout. It leaves `12` in the result cell —
`GoLean.Quorum.committedIndexRef [1] ackedOneKnown`. -/
theorem wp_committedIndex_body {ca cba la lba ra : Addr}
    {cty lty : Option Ty} {k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData
          #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.interface ⟨"main.AckedIndexer"⟩),
                  .interface (.defined ⟨"main.mapAckIndexer"⟩)
                    (.map ⟨some (.base lba)⟩)⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData
          #[(.int 1 .uint64, .int 12 .uint64)]⟩ : HeapCell)
      ∗ ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec committedIndexImpl.body
            [[("$res0", Loc.base ra), ("l", Loc.base la), ("c", Loc.base ca)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hc, Hcb, Hl, Hlb, Hr, Hcont⟩
  rw [committedIndexImpl_body_eq]
  go_walk with [committedIndexStmts_toList]
  -- `n := len(c)`
  go_walk_step (wp_ci_len (cba := cba) (cty := cty)
    (entries := #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]) (by decide) rfl)
    as [na]
  go_walk
  -- `if n == 0 { return math.MaxUint64 }`, not taken
  go_walk_step (wp_ci_emptyIf (na := na) (n := 1) rfl
    (fun σ => by
      simp [applyStrictOp, valueEq, valueEqFuel, typeResolutionFuel,
        Bind.bind, Except.bind]))
  go_walk
  -- `var stk [7]uint64` and `var srt []uint64`
  go_walk_step wp_ci_stkDecl as [sta]
  go_walk
  go_walk_step wp_ci_srtDecl as [sra]
  go_walk
  -- `if len(stk) >= n { srt = stk[:n] }`, taken
  go_walk_step (wp_ci_fitIf_one (na := na) (sta := sta) (sra := sra) rfl rfl rfl)
  go_walk
  -- the voter loop
  go_walk_step (wp_ci_loop_one (na := na) (ca := ca) (cba := cba) (la := la)
    (lba := lba) (sra := sra) (sta := sta) (cty := cty) (lty := lty)
    hprog hmeths htypes rfl rfl rfl rfl)
  -- ONE step (`wp_stmt_op_first` matches every `Config.exec`, so an
  -- unbounded walk would descend into `slices.Sort` instead of taking the
  -- tail segment whole)
  go_walk 1
  -- `slices.Sort`, `pos`, `return Index(srt[pos])`
  -- (`wp_ci_tail_one`'s own continuation wand IS `Hcont`, so framing closes
  -- the segment)
  go_walk_step (wp_ci_tail_one (na := na) (sra := sra) (sta := sta) (ra := ra)
    htypes rfl rfl rfl)

/-- **The `CommittedIndex` callsite** inside `run` — the STATIC frame
entry into a method on a concrete receiver, with the second argument BOXED
at the callsite (`.toInterface`: `mapAckIndexer` values become
`AckedIndexer` interface values, the boxing the later dynamic dispatch
unboxes), the body walk, and the one-result frame exit at a NAMED result
type. -/
theorem wp_committedIndexCall {ca cba la lba ta : Addr} {cty lty : Option Ty}
    {env k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList)
    (hres : LocalEnv.lookup env "$c3" = some (.base ta))
    (hc : LocalEnv.lookup env "c" = some (.base ca))
    (hl : LocalEnv.lookup env "l" = some (.base la)) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData
          #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                  .map ⟨some (.base lba)⟩⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData
          #[(.int 1 .uint64, .int 12 .uint64)]⟩ : HeapCell)
      ∗ ta.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec
            (.call #[.var "$c3"] ⟨"main.MajorityConfig.CommittedIndex"⟩
              #[.var "c",
                .toInterface (.interface ⟨"main.AckedIndexer"⟩)
                  (.defined ⟨"main.mapAckIndexer"⟩) (.var "l")]) env k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hc, Hcb, Hl, Hlb, Ht, Hcont⟩
  -- the target and the receiver
  go_walk
  -- the second argument, BOXED at the callsite (`.toInterface`)
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
  -- the STATIC frame entry (two arguments, one result, no dynamic dispatch)
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
  -- the body
  go_walk_step (wp_committedIndex_body (ca := a₀) (cba := cba) (la := a₁)
    (lba := lba) (ra := a₂) (cty := cty) (lty := lty) hprog hmeths htypes)
  -- the one-result frame exit at a NAMED result type
  go_walk_step (wp_frame_return₁ (ta := ta) (ra := a₂)
    (rcell := ⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩)
    (tcell := ⟨some (.defined ⟨"main.Index"⟩), .int 0 .uint64⟩)
    (tcell' := ⟨some (.defined ⟨"main.Index"⟩), .int 12 .uint64⟩)
    (hstore := fun σ ht hlk => by
      rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
        (rfl (a := σ.methods))] at hlk ⊢
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        typeResolutionFuel, QuorumPin.typeEnv_Index, Bind.bind, Except.bind,
        show IntKind.uint64.normalize 12 = 12 from by decide]))
  go_walk_finish Hcont

/-- **`run`'s body** — the thin wrapper the corpus driver calls: declare
`$c3 : main.Index`, call `c.CommittedIndex(l)`, convert the named result
back to `uint64` and return it. -/
theorem wp_run_body {ca cba la lba ra : Addr} {cty lty : Option Ty} {k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList) :
    ca.id ↦ (⟨some (.defined ⟨"main.MajorityConfig"⟩),
              .map ⟨some (.base cba)⟩⟩ : HeapCell)
      ∗ cba.id ↦ (⟨cty, .mapData
          #[(.int 1 .uint64, .struct ⟨"struct{}"⟩ #[])]⟩ : HeapCell)
      ∗ la.id ↦ (⟨some (.defined ⟨"main.mapAckIndexer"⟩),
                  .map ⟨some (.base lba)⟩⟩ : HeapCell)
      ∗ lba.id ↦ (⟨lty, .mapData
          #[(.int 1 .uint64, .int 12 .uint64)]⟩ : HeapCell)
      ∗ ra.id ↦ (⟨some (.int .uint64), .int 0 .uint64⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int .uint64), .int 12 .uint64⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec runImpl.body
            [[("$res0", Loc.base ra), ("l", Loc.base la), ("c", Loc.base ca)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hc, Hcb, Hl, Hlb, Hr, Hcont⟩
  rw [runImpl_body_eq]
  go_walk
  unfold runCallSeq
  go_walk
  -- `var $c3 main.Index` — named, because the callsite below takes its cell
  go_walk_step (wp_init (v := .int 0 .uint64) (hdef := fun σ ht => by
    rw [execState_pin_eq (ht.trans htypes) (rfl (a := σ.functions))
      (rfl (a := σ.methods))]
    simp [defaultValue, defaultValueFuel, typeResolutionFuel,
      QuorumPin.typeEnv_Index])) as [c3a]
  -- ONE step: the callsite below is taken WHOLE, so the walk must not start
  -- evaluating the call's target and arguments
  go_walk 1
  -- `$c3 = c.CommittedIndex(l)`
  go_walk_step (wp_committedIndexCall (ca := ca) (cba := cba) (la := la)
    (lba := lba) (ta := c3a) (cty := cty) (lty := lty) hprog hmeths htypes
    rfl rfl rfl)
  go_walk
  unfold runResSeq
  go_walk
  -- `return uint64($c3)` — the conversion is state-independent at a BASIC
  -- target type, so the walk takes it; only the store needs a witness
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.int .uint64), .int 0 .uint64⟩)
    (newcell := ⟨some (.int .uint64), .int 12 .uint64⟩)
    (fun σ _ht hlk => by
      have h := storeLoc_int_any (mkind := .uint64) hlk 12
      rw [show IntKind.uint64.normalize 12 = 12 from by decide] at h
      exact h))
  go_walk_finish Hcont

/-- **The driver body** — `committedOneKnown`: build `MajorityConfig{1:{}}`
and `mapAckIndexer{1:12}` with two `make(map…)`s (each ALLOCATING its data
cell inside the apply step) and two `m[k] = v` writes, call `run`, return
its answer. -/
theorem wp_oneKnown_body {ra : Addr} {k}
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList) :
    ra.id ↦ (⟨some (.int .uint64), .int 0 .uint64⟩ : HeapCell)
      ∗ (ra.id ↦ (⟨some (.int .uint64), .int 12 .uint64⟩ : HeapCell)
          -∗ WP (Config.returning k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec oneKnownImpl.body [[("$res0", Loc.base ra)]] k)
          @ s ; E {{ Φ }} := by
  iintro ⟨Hr, Hcont⟩
  rw [oneKnownImpl_body_eq]
  go_walk
  -- `c := MajorityConfig{1: {}}`
  unfold okCfgSeq
  go_walk
  go_walk_step (wp_init (v := .map ⟨none⟩) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel])) as [c10a, Hc10]
  go_walk
  go_walk_step (wp_make_map (a := c10a)
    (oldcell := ⟨some (.map (.int .uint64) (.defined ⟨"struct{}"⟩)),
                 .map ⟨none⟩⟩)
    (newcell := fun fa => ⟨some (.map (.int .uint64) (.defined ⟨"struct{}"⟩)),
                           .map ⟨some (.base fa)⟩⟩)
    (hstore := fun σ fa _ht hlk => by
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind, typeResolutionFuel])) as [cfgba, Hcfgb, Hc10]
  -- `c[1] = struct{}{}`
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
        mapEntryIndex?,
        normalizeValueForTy, normalizeValueForTyFuel, typeResolutionFuel,
        QuorumPin.typeEnv_structEmpty, normalizeStructValueWith,
        normalizeFieldsWith, checkKeyHashable, valueHashability,
        coerceStoredValue, storeLoc, Functor.map, Except.map,
        Bind.bind, Except.bind,
        show IntKind.uint64.normalize 1 = 1 from by decide])) as [Hcfgb]
  -- `l := mapAckIndexer{1: 12}`
  go_walk
  unfold okAckSeq
  go_walk
  go_walk_step (wp_init (v := .map ⟨none⟩) (hdef := fun σ _ => by
    simp [defaultValue, defaultValueFuel, typeResolutionFuel])) as [c11a, Hc11]
  go_walk
  go_walk_step (wp_make_map (a := c11a)
    (oldcell := ⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
                 .map ⟨none⟩⟩)
    (newcell := fun fa => ⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
                           .map ⟨some (.base fa)⟩⟩)
    (hstore := fun σ fa _ht hlk => by
      simp [storeLoc, hlk, normalizeValueForTy, normalizeValueForTyFuel,
        Bind.bind, Except.bind, typeResolutionFuel])) as [ackba, Hackb, Hc11]
  -- `l[1] = 12`
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
        show IntKind.uint64.normalize 12 = 12 from by decide])) as [Hackb]
  -- `r := run(c, l)`
  go_walk
  unfold okCallSeq
  -- two steps, then `var r uint64` BY NAME (the callsite below takes its cell)
  go_walk 2
  go_walk_step wp_init_int as [c12a, Hc12]
  -- the target and the two map arguments
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
  go_walk_step (wp_run_body (ca := b₀) (cba := cfgba) (la := b₁) (lba := ackba)
    (ra := b₂) hprog hmeths htypes)
  go_walk_step (wp_frame_return_int (ta := c12a) (ra := b₂) (kind := .uint64)
    (tkind := .uint64) (m := 12))
  -- `return r`
  go_walk
  unfold okResSeq
  go_walk
  go_walk_step (wp_assign_store
    (oldcell := ⟨some (.int .uint64), .int 0 .uint64⟩)
    (newcell := ⟨some (.int .uint64), .int 12 .uint64⟩)
    (fun σ _ht hlk => by
      have h := storeLoc_int_any (mkind := .uint64) hlk 12
      rw [show IntKind.uint64.normalize 12 = 12 from by decide] at h
      exact h))
  go_walk_finish Hcont

/-- **The `committedOneKnown()` callsite** — the outermost frame: one
target cell, no arguments, `wp_call_enter_ret1` in, the driver body, and
the int frame exit that delivers `12` to the caller's cell. -/
theorem wp_oneKnownCall {ta : Addr} {w : GoValue} {env k}
    (hres : LocalEnv.lookup env "$callres" = some (.base ta))
    (hprog : GoCoreGS.prog GF = quorumLowered.funcs)
    (hmeths : GoCoreGS.methods GF = quorumLowered.methods)
    (htypes : GoCoreGS.types GF = quorumLowered.typeDefs.toList) :
    ta.id ↦ (⟨some (.int .uint64), w⟩ : HeapCell)
      ∗ (ta.id ↦ (⟨some (.int .uint64), .int 12 .uint64⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.exec (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[])
            env k) @ s ; E {{ Φ }} := by
  iintro ⟨Ht, Hcont⟩
  -- the one target cell, no arguments
  go_walk
  -- the outermost frame entry
  go_walk_step (wp_call_enter_ret1 (func := QuorumPin.oneKnownImpl)
    (dv := .int 0 .uint64)
    (hfind := by rw [hprog]; exact QuorumPin.oneKnownImpl_find)
    (hargs := QuorumPin.oneKnownImpl_args)
    (hres := QuorumPin.oneKnownImpl_results)
    (hnodisp := fun σ hm => by
      simp only [dynamicDispatch?, methodInfoByFuncId?, hm.trans hmeths]
      simp +decide [QuorumPin.quorumMethods_eq, Bind.bind, Except.bind])
    (hdef := fun σ _ => by
      simp [defaultValue, defaultValueFuel, typeResolutionFuel])) as [rra]
  -- the driver body, and the int frame exit
  go_walk_step (wp_oneKnown_body (ra := rra) hprog hmeths htypes)
  go_walk_step (wp_frame_return_int (ta := ta) (ra := rra) (kind := .uint64)
    (tkind := .uint64) (m := 12))
  go_walk_finish Hcont

end

end GoLean.Iris.GoldenQuorum

namespace GoLean.Surface

open GoLean.GoCore GoLean.Quorum

/- `quorumOneKnownFuncSpec_statement`, `quorumOneKnownNotEleven_statement`,
`ackedIndexerPre` and `quorumAckedIndexFuncSpec2_statement` moved to
`Specs/Statements.lean` — the Iris-free statement layer (comparator-judge
sprint, 2026-08-02): headline statements must be importable without Iris
in the import closure. The theorems that discharge them stay below. -/

/-! ### Non-vacuity of the discharge

A `GoSpec` quantifies over *admissible* initial states (`InitialSplit`).
If no state were admissible the judgment would be true of anything — the
vacuity class the project's gate exists to catch. The lemmas below
exhibit one: a concrete four-cell heaplet satisfying the discharged
precondition at distinct addresses. (`goldenReturnsTwo` plays the same
role for the unary golden spec, by reading a concrete run out of it.) -/

/-! The three `Heaplet` facts these need, stated over the bridge's
`PartialMap` API (the surface's `ExtTreeMap` operations ARE the bridge's,
`SurfaceBridge.heaplet_get?_eq`/`heaplet_insert_eq`). -/

theorem heaplet_get?_empty {k : Nat} : (∅ : Heaplet).get? k = none := by
  rw [heaplet_get?_eq]
  exact LawfulPartialMap.get?_empty (M := GoHeapF) (k := k)

theorem heaplet_get?_insert_self {m : Heaplet} {k : Nat} {v : HeapCell} :
    (m.insert k v).get? k = some v := by
  rw [heaplet_get?_eq, heaplet_insert_eq]
  exact LawfulPartialMap.get?_insert_eq rfl

theorem heaplet_get?_insert_ne {m : Heaplet} {k k' : Nat} {v : HeapCell}
    (h : k ≠ k') : (m.insert k v).get? k' = m.get? k' := by
  rw [heaplet_get?_eq, heaplet_insert_eq, heaplet_get?_eq]
  exact get?_insert_ne h

/-- Prepending a FRESH cell to a satisfying heaplet satisfies the
separating conjunction with that cell's points-to. General — no program,
no address, no assertion fixed. -/
theorem sat_sep_insert {h : Heaplet} {ℓ : Nat} {c : HeapCell} {P : HProp}
    (hfresh : h.get? ℓ = none) (hP : sat h P) :
    sat (h.insert ℓ c) (.sep (.pointsTo ℓ c) P) := by
  refine ⟨(∅ : Heaplet).insert ℓ c, h, rfl, hP, ?_, ?_⟩
  · intro k
    by_cases hk : k = ℓ
    · exact Or.inr (hk ▸ hfresh)
    · exact Or.inl (by
        rw [heaplet_get?_insert_ne (fun he => hk he.symm), heaplet_get?_empty])
  · intro k c'
    by_cases hk : k = ℓ
    · subst hk
      rw [heaplet_get?_insert_self, heaplet_get?_insert_self, hfresh]
      simp
    · rw [heaplet_get?_insert_ne (fun he => hk he.symm),
        heaplet_get?_insert_ne (fun he => hk he.symm), heaplet_get?_empty]
      simp

/-- **The discharged precondition is satisfiable** (at `ra = 0`,
`rb = 1`, `ma = 2`, `mba = 3`, and ANY prior target values): the
`quorumAckedIndexFuncSpec2` statement speaks about states that exist, so
its `∀`-over-admissible-states is not vacuous. -/
theorem quorumAckedIndexPre_satisfiable (w₁ w₂ : GoValue) :
    ∃ h : Heaplet, sat h
      (.sep (.pointsTo 0 ⟨some (.int .uint64), w₁⟩)
        (.sep (.pointsTo 1 ⟨some .bool, w₂⟩) (ackedIndexerPre 2 3))) := by
  refine ⟨((((∅ : Heaplet).insert 3
      ⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
       .mapData #[(.int 3 .uint64, .int 12 .uint64)]⟩).insert 2
      ⟨some (.defined ⟨"main.mapAckIndexer"⟩), .map ⟨some (.base ⟨3⟩)⟩⟩).insert 1
      ⟨some .bool, w₂⟩).insert 0 ⟨some (.int .uint64), w₁⟩, ?_⟩
  refine sat_sep_insert ?_ (sat_sep_insert ?_ (sat_sep_insert ?_ rfl))
  · rw [heaplet_get?_insert_ne (by omega), heaplet_get?_insert_ne (by omega),
      heaplet_get?_insert_ne (by omega), heaplet_get?_empty]
  · rw [heaplet_get?_insert_ne (by omega), heaplet_get?_insert_ne (by omega),
      heaplet_get?_empty]
  · rw [heaplet_get?_insert_ne (by omega), heaplet_get?_empty]

/-- **THE DISCHARGE — the first `GoFuncSpec2` result** (quorum pilot
phase 4, slice 5). The per-program obligation is exactly the WP proof
(`wp_ackedIndexCall`), as for every surface discharge; the exit pipe
(`goSpec_of_wp`) supplies the frame closure and progress. What this
proves about REAL Go: a method called on a concrete receiver, its
`(T, bool)` comma-ok result pair delivered to the caller's cells by the
machine's own frame-exit protocol, over the frontend's actual lowering of
etcd-io/raft's `quorum` package. -/
theorem quorumAckedIndexFuncSpec2 : quorumAckedIndexFuncSpec2_statement := by
  unfold quorumAckedIndexFuncSpec2_statement GoFuncSpec2 ackedIndexerPre
  intro ma mba ra rb w₁ w₂ _hne
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths htypes
  simp only [embed]
  iintro ⟨Hta, Htb, Hm, Hmb⟩
  iapply (GoLean.Iris.GoldenQuorum.wp_ackedIndexCall (ma := ⟨ma⟩) (mba := ⟨mba⟩)
    (ta := ⟨ra⟩) (tb := ⟨rb⟩) (w₁ := w₁) (w₂ := w₂)
    (mty := some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)))
    (q := 3) (v := 12) rfl rfl rfl
    hprog hmeths htypes (by decide) (by decide))
  isplitl [Hm]
  · iexact Hm
  isplitl [Hmb]
  · iexact Hmb
  isplitl [Hta]
  · iexact Hta
  isplitl [Htb]
  · iexact Htb
  iintro ⟨Hta, Htb⟩
  iapply (wp_value' (v := ()))
  iexists (12 : Int)
  iexists true
  isplitl [Hta]
  · iexact Hta
  isplitl [Htb]
  · iexact Htb
  · ipureintro
    exact ⟨rfl, rfl⟩


/-! ## THE ARC'S NAMED GOAL

`docs/2026-07-30_quorum-pilot-arc.md` THE GOAL: a kernel-checked theorem
about the REAL `etcd-io/raft` `(MajorityConfig).CommittedIndex`, over the
frontend's ACTUAL lowering, whose answer is the declarative quorum spec's.
Scope, stated once and not softened: **one voter** (`n = 1`), so the map
range's nondeterminism is degenerate (a single iteration order) and the
`len(stk) >= n` branch is the reslice one. The three-voter walk — real
branching in the range, a non-trivial sort, the `pos` arithmetic biting —
is the recorded next widening. -/

/-- **THE THEOREM.** `committedOneKnown()` — the pinned lowering of the
real quorum driver — returns `12`, at `GoFuncSpec` strength: into any
caller cell, over any prior value, in any admissible heap, beside any
frame, through the exit pipe (triple + progress). The per-program
obligation is the WP walk `wp_oneKnownCall`, which composes only general
laws over `GoldenQuorum.quorumLowered`. -/
theorem quorumOneKnownFuncSpec : quorumOneKnownFuncSpec_statement := by
  unfold quorumOneKnownFuncSpec_statement GoFuncSpec
  intro ra w
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths htypes
  simp only [embed]
  iintro ⟨H0, -⟩
  iapply (GoLean.Iris.GoldenQuorum.wp_oneKnownCall (ta := ⟨ra⟩) (w := w)
    rfl hprog hmeths htypes)
  isplitl [H0]
  · iexact H0
  iintro H12
  iapply (wp_value' (v := ()))
  iexists (12 : Int)
  isplitl [H12]
  · iexact H12
  · ipureintro
    rfl

/-- **THE COROLLARY THAT NAMES THE GOAL**: the machine's answer *is* a
committed index. The postcondition is no longer a number but the
declarative spec of `deps/raft/quorum/majority.go` — committedness plus
maximality (`GoLean.Quorum.IsCommittedIndex`) — discharged on the
one-voter instance by `isCommittedIndex_oneKnown`, which is itself the
proven general agreement theorem `committedIndexRef_meets_spec` applied to
the reference. So the chain is closed end to end: real Go source →
frontend lowering (pinned) → machine walk (this WP proof) → declarative
quorum spec, with no unproven link. -/
theorem quorumOneKnownMeetsSpec :
    GoFuncSpec quorumLowered.typeDefs.toList quorumLowered.funcs
      quorumLowered.methods ⟨"committedOneKnown"⟩ .uint64 #[] .emp
      (fun n => .pure (0 ≤ n ∧
        GoLean.Quorum.IsCommittedIndex [1] GoLean.Quorum.ackedOneKnown
          n.toNat)) := by
  unfold GoFuncSpec
  intro ra w
  refine goSpec_of_wp ?_
  intro _inst hprog hmeths htypes
  simp only [embed]
  iintro ⟨H0, -⟩
  iapply (GoLean.Iris.GoldenQuorum.wp_oneKnownCall (ta := ⟨ra⟩) (w := w)
    rfl hprog hmeths htypes)
  isplitl [H0]
  · iexact H0
  iintro H12
  iapply (wp_value' (v := ()))
  iexists (12 : Int)
  isplitl [H12]
  · iexact H12
  · ipureintro
    exact ⟨by decide, GoLean.Quorum.isCommittedIndex_oneKnown⟩


/-! ### The first-order readout, and the negative twin

`GoFuncSpec` is a separation-logic statement; the corpus-facing claim is
first-order ("this run leaves 12 at this address"). The pair below is the
golden precedent's (`goldenReturnsTwo`/`goldenNotThree`) at the quorum
driver: read the triple out at a pinned address, then refute 11 in two
lines. Both are run-CONDITIONED — a `GoTriple` says nothing about a
program that fails to terminate, so the unconditional `¬ GoFuncSpec` form
of the target `quorumOneKnownNotEleven_statement` (phase 4, `39891ae`) is not
refutable from the triple alone: refuting it demands EXHIBITING a
terminating run (a kernel evaluation of the interpreter over the whole
pinned program), which is a separate cost and stays recorded as owed. -/

/- `quorumOut`/`quorumOutEnv` (the readout's seeded state) moved to
`Specs/Statements.lean` — the readout THEOREM statement references them. -/

/-- **The first-order readout**: every terminating run of
`$callres = committedOneKnown()` from the seeded one-cell state leaves
`uint64(12)` at base address 0. -/
theorem quorumOneKnownReturnsTwelve
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel quorumOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 12 .uint64) := by
  have htriple := (quorumOneKnownFuncSpec 0 (.int 0 .uint64)).1
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
          cases h0)⟩⟩ }
    fuel ch σf ch' hrun
  obtain ⟨h, _hd, hsub, _hF, hsat⟩ := hres
  obtain ⟨n, h₁, h₂, hp1, hp2, _hdisj, hcov⟩ := hsat
  obtain ⟨hn12, rfl⟩ := hp2
  subst hn12
  have hget : h.get? 0 = some ⟨some (.int .uint64), .int 12 .uint64⟩ := by
    rw [hcov]
    exact Or.inl (by rw [hp1]; exact heaplet_get?_insert_self)
  have := hsub 0 ⟨some (.int .uint64), .int 12 .uint64⟩ hget
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at this
  exact loadLoc_base_of_lookup this

/-- **The negative twin** — the two-line corollary the golden precedent
predicts: no terminating run leaves `11`. This is what stops a trivialized
postcondition from passing for the real one. -/
theorem quorumOneKnownNotEleven
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel quorumOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := quorumOut, nextAddr := 1 } ch
        (.call #[.var "$callres"] ⟨"committedOneKnown"⟩ #[])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) ≠ .ok (.int 11 .uint64) := by
  intro h11
  have h12 := quorumOneKnownReturnsTwelve fuel ch σf ch' hrun
  have := h12.symm.trans h11
  injection this with hval
  injection hval with hn _
  exact absurd hn (by decide)

/-! ### The two-cell readout for the `GoFuncSpec2` result (audit
response 2026-08-01)

The TCB/layering doctrine (`docs/2026-08-01_tcb-and-layering-doctrine.md`
§1, ladder rung 2) makes the first-order readout mandatory beside any
`GoFuncSpec*` headline; `quorumAckedIndexFuncSpec2` predates the doctrine
and shipped without one (pre-merge audit finding). This is the
`quorumOneKnownReturnsTwelve` pattern at the two-result protocol: a
concrete four-cell instance (the satisfiability witness's addresses), the
triple read out at BOTH pinned target cells. -/

/- `ackedIndexOut`/`ackedIndexOutEnv` (the two-cell readout's seeded state)
moved to `Specs/Statements.lean`. -/

/-- **The two-cell first-order readout**: every terminating run of
`$callres0, $callres1 = m.AckedIndex(3)` from the seeded four-cell state
leaves `uint64(12)` at base address 0 AND `true` at base address 1 — the
comma-ok pair, observed by `execStmt`/`loadLoc` with no separation logic
in the statement. -/
theorem quorumAckedIndexReturnsTwelveTrue
    (fuel : Nat) (ch : Choices) (σf : ExecState) (ch' : Choices)
    (hrun : execStmt fuel ackedIndexOutEnv
        { types := quorumLowered.typeDefs.toList,
          functions := quorumLowered.funcs, methods := quorumLowered.methods,
          heap := ackedIndexOut, nextAddr := 4 } ch
        (.call #[.var "$callres0", .var "$callres1"]
          ⟨"main.mapAckIndexer.AckedIndex"⟩ #[.var "m", .intLit 3 .uint64])
      = .ok (.normal σf, ch')) :
    loadLoc σf (.base ⟨0⟩) = .ok (.int 12 .uint64)
      ∧ loadLoc σf (.base ⟨1⟩) = .ok (.bool true) := by
  have htriple := (quorumAckedIndexFuncSpec2 2 3 0 1 (.int 0 .uint64)
    (.bool false) (by omega)).1
  have hres := htriple ackedIndexOut 4 (heapletOf ackedIndexOut) (∅ : Heaplet)
    { bounded := by
        intro n hn
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
        rfl
      disj := fun k => .inr heaplet_get?_empty
      cover := fun k c => by
        constructor
        · exact fun h => .inl h
        · rintro (h | h)
          · exact h
          · rw [heaplet_get?_empty] at h
            cases h
      sat_pre := by
        show sat (((((∅ : Heaplet).insert 3
            ⟨some (.map (.int .uint64) (.defined ⟨"main.Index"⟩)),
             .mapData #[(.int 3 .uint64, .int 12 .uint64)]⟩).insert 2
            ⟨some (.defined ⟨"main.mapAckIndexer"⟩),
             .map ⟨some (.base ⟨3⟩)⟩⟩).insert 1
            ⟨some .bool, .bool false⟩).insert 0
            ⟨some (.int .uint64), .int 0 .uint64⟩) _
        refine sat_sep_insert ?_ (sat_sep_insert ?_ (sat_sep_insert ?_ rfl))
        · rw [heaplet_get?_insert_ne (by omega),
            heaplet_get?_insert_ne (by omega),
            heaplet_get?_insert_ne (by omega), heaplet_get?_empty]
        · rw [heaplet_get?_insert_ne (by omega),
            heaplet_get?_insert_ne (by omega), heaplet_get?_empty]
        · rw [heaplet_get?_insert_ne (by omega), heaplet_get?_empty] }
    fuel ch σf ch' hrun
  obtain ⟨h, _hd, hsub, _hF, hsat⟩ := hres
  obtain ⟨n, b, h₁, h₂, hp1, hp2, _hdisj, hcov⟩ := hsat
  obtain ⟨h₃, h₄, hp3, hp4, _hdisj2, hcov2⟩ := hp2
  obtain ⟨⟨hn12, hbt⟩, rfl⟩ := hp4
  subst hn12
  subst hbt
  have hget0 : h.get? 0 = some ⟨some (.int .uint64), .int 12 .uint64⟩ := by
    rw [hcov]
    exact Or.inl (by rw [hp1]; exact heaplet_get?_insert_self)
  have hget1 : h.get? 1 = some ⟨some .bool, .bool true⟩ := by
    rw [hcov]
    refine Or.inr ?_
    rw [hcov2]
    exact Or.inl (by rw [hp3]; exact heaplet_get?_insert_self)
  have h0 := hsub 0 ⟨some (.int .uint64), .int 12 .uint64⟩ hget0
  have h1 := hsub 1 ⟨some .bool, .bool true⟩ hget1
  rw [heaplet_get?_eq, heapletOf_eq_heapToMap, get?_heapToMap] at h0 h1
  exact ⟨loadLoc_base_of_lookup h0, loadLoc_base_of_lookup h1⟩

end GoLean.Surface
