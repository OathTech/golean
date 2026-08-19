import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.Adequacy
import Iris.ProofMode
import Iris.BI.Lib.GenHeap
import Std.Data.ExtTreeMap
import Iris.Std.PartialMap
import Iris.Std.FromMathlib
import Iris.Std.GenSetsInstances
import GoLean.GoCore.MachineSound
import GoLeanProofs.HeapBridge
import GoLeanProofs.Laws.Eval
import GoLeanProofs.Laws.Control
import GoLeanProofs.Tactics.GoWalk

/-!
# Map-range laws — THE FIRST NONDETERMINISTIC WP LAW (quorum pilot
phase 4, 2026-07-31)

`Step.mapIterNext` chooses ANY index of the remaining snapshot and
allocates the iteration variable — the machine's first genuinely
nondeterministic rule to get a WP law (the D2/D3 "bites at the first
nondet feature" moment, `TODO.md`). The law's premise supplies the
continuation for ALL (index, allocated address) pairs; safety needs one
witness successor (index 0). Everything the deterministic laws pinned
via `step_det` becomes a per-successor case analysis here.

v1 scope: the KEY-ONLY form (`for id := range c` — the quorum shape);
key/value iteration gets its law when a walk needs it.

**These laws are conformance statements about the machine AS IT STANDS,
and the machine here is known non-conformant: `docs/BUGS.md` BUG-005.**
`mapRangeEntries` snapshots the whole entry array, so iteration observes
neither a `delete`/`clear` nor a value UPDATE performed inside the loop
body, where Go observes both. The laws are accurate — and they will need
reshaping when BUG-005's machine surgery lands (`Cont.mapIterK` carries
the map's base location; the pick-next step skips absent keys and
re-reads values live), which BUG-005 already anticipates. Cross-referenced
here because it was not (pre-merge audit 2026-07-31, finding 1).
-/

open Iris Iris.ProgramLogic Iris.Std Iris.Std.PartialMap
open GoLean GoLean.GoCore GoLean.GoCore.Machine

namespace GoLean.Iris

set_option linter.unusedSimpArgs false

section
variable {GF : BundledGFunctors} {hlc : HasLC} [GoCoreGS hlc GF]
variable {s : Stuckness} {E : CoPset} {Φ : Unit → IProp GF}

/-- `bindIterVars` computation, key-only: one normalized alloc, the key
variable declared in a pushed scope. -/
theorem bindIterVars_key_only {env : LocalEnv} {σ : ExecState}
    {kid : String} {keyTy valTy : Ty} {key value kv : GoValue}
    (hnorm : normalizeValueForTy σ keyTy key = .ok kv) :
    bindIterVars env.pushScope σ (some kid) none keyTy valTy key value
      = .ok (env.pushScope.declare kid (.base ⟨σ.nextAddr⟩),
          { σ with heap := Heap.set σ.heap (.base ⟨σ.nextAddr⟩) ⟨some keyTy, kv⟩,
                   nextAddr := σ.nextAddr + 1 }) := by
  unfold bindIterVars
  simp [hnorm, Bind.bind, Except.bind, ExecState.alloc, ExecState.freshLoc]

/-- `wp_pure_det` with DIRECT determinism instead of `Config.choiceFree`
(which conservatively marks every `mapIterK` continuation as a choice
point, including the empty snapshot — where `mapIterNext` cannot fire
and the step is in fact unique). -/
private theorem wp_pure_det' {c₀ c₁ : Config}
    (hnv : ToVal.toVal c₀ = (none : Option Unit))
    (hstep : ∀ σ : ExecState, Step c₀ σ c₁ σ)
    (hdet : ∀ (σ : ExecState) c' σ', Step c₀ σ c' σ' → c' = c₁ ∧ σ' = σ) :
    (|={E}[E]▷=> £ 1 -∗ WP c₁ @ s ; E {{ Φ }}) ⊢ WP c₀ @ s ; E {{ Φ }} := by
  iintro H
  iapply (wp_lift_pure_det_step_no_fork (E₂ := E) (e₂ := c₁)
    (Hsafe := by
      intro σ
      cases s
      · exact ⟨[], c₁, σ, [], GoPrimStep.step (hstep σ)⟩
      · exact hnv)
    (Hpuredet := by
      intro σ obs e₂' σ₂ eₜ' h
      cases h with
      | step st =>
        obtain ⟨he, hs⟩ := hdet σ _ _ st
        exact ⟨rfl, hs, he, rfl⟩))
  iexact H

/-- **The done step at a NIL map** (base `none`): no cell exists, the
candidate set is empty by computation for EVERY produced set, and the
frame pops deterministically. -/
@[go_walk_law]
theorem wp_map_iter_done_nil {kid : Option String} {vv : Option String}
    {keyTy valTy : Ty} {body : Stmt} {produced start : Array GoValue}
    {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.mapIterK kid vv keyTy valTy body none produced start env k))
        @ s ; E {{ Φ }} :=
  wp_pure_det' rfl (fun _ => Step.mapIterDone rfl)
    (fun σ c' σ' hst => by
      cases hst with
      | mapIterDone _ => exact ⟨rfl, rfl⟩
      | mapIterNext hidx hcands _ _ =>
          rw [show mapIterCandidates σ keyTy valTy none produced = .ok #[]
            from rfl] at hcands
          injection hcands with hcands
          rw [← hcands] at hidx
          exact absurd hidx (by simp)
      | mapIterStop hcands hne _ =>
          rw [show mapIterCandidates σ keyTy valTy none produced = .ok #[]
            from rfl] at hcands
          injection hcands with hcands
          exact absurd (by rw [← hcands]; rfl) hne)

/-- **The done step at an OWNED cell** (BUG-005 (L)): doneness is a
STATE fact now — the caller supplies the candidates-empty computation
against the owned cell (`hcands`), the machine loads and agrees. -/
theorem wp_map_iter_done {kid : Option String} {vv : Option String}
    {keyTy valTy : Ty} {body : Stmt} {ba : Addr} {cell : HeapCell}
    {produced start : Array GoValue} {env k}
    (hcands : ∀ (σ : ExecState), σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base ba) = some cell →
      mapIterCandidates σ keyTy valTy (some (.base ba)) produced = .ok #[]) :
    ba.id ↦ cell
      ∗ (ba.id ↦ cell -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.next (.mapIterK kid vv keyTy valTy body
            (some (.base ba)) produced start env k)) @ s ; E {{ Φ }} := by
  iapply wp_det_step_keep (P := iprop(ba.id ↦ cell))
    (c₁ := Config.next k) (hnv := rfl)
  intro σ₁ _hfns _hmeths htypes
  iintro ⟨Hσ, Hpt⟩
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) ba.id = some cell⌝ $$ [Hσ Hpt]
  · icases genHeap_valid $$ [$Hσ $Hpt] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base ba) = some cell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hc := hcands σ₁ htypes hlook
  imodintro
  ipureintro
  refine ⟨Step.mapIterDone hc, ?_⟩
  intro c' s' hst
  cases hst with
  | mapIterDone _ => exact ⟨rfl, rfl⟩
  | mapIterNext hidx hcands' _ _ =>
      rw [hc] at hcands'
      injection hcands' with hcands'
      rw [← hcands'] at hidx
      exact absurd hidx (by simp)
  | mapIterStop hcands' hne _ =>
      rw [hc] at hcands'
      injection hcands' with hcands'
      exact absurd (by rw [← hcands']; rfl) hne

/-- Dispatch a map range: evaluate the map expression. -/
@[go_walk_law]
theorem wp_map_range_start {keyVar valVar : Option String}
    {mapExpr : Expr} {keyTy valTy : Ty} {body : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE mapExpr env
        (.mapRangeK keyVar valVar keyTy valTy body env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.mapRange keyVar valVar mapExpr keyTy valTy body) env k)
        @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.mapRange)

/-- **THE NONDETERMINISTIC STEP, key-only form (BUG-005 (L))**: with a
NONEMPTY candidate set over the OWNED map cell, the machine picks ANY
candidate index `i`, pushes its key into the produced set, and
allocates the key cell at a machine-chosen address. The premise
supplies the continuation for EVERY such choice (`∀ i pa`); safety is
witnessed at `i = 0`.

`hcands`/`hmand` are the pick-time STATE facts against the owned cell,
with the `σ.types` GHOST PIN (Ghost.lean's rule): the candidates load
carries the fail-closed normalization validation (the retired
snapshot's check, moved to the pick — this is also where the old
`hnorm` premise went: normalization now comes OUT of `hcands`).
`hmand = true` is the MUTATION-FREE shape's fact (every candidate is a
never-removed start key), and is what excludes the STOP step here: a
range whose body deletes from the map needs the stop-admitting law,
which lands with the first walk that needs it (kit obligation,
arc log). -/
theorem wp_map_iter_next_key {kid : String} {keyTy valTy : Ty}
    {body : Stmt} {ba : Addr} {cell : HeapCell}
    {produced start : Array GoValue} {rem : Array (GoValue × GoValue)}
    {env k}
    (hne : 0 < rem.size)
    (hcands : ∀ (σ : ExecState), σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base ba) = some cell →
      mapIterCandidates σ keyTy valTy (some (.base ba)) produced = .ok rem)
    (hmand : ∀ (σ : ExecState), σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base ba) = some cell →
      mapIterMandatoryRemains σ keyTy rem start = .ok true) :
    iprop(ba.id ↦ cell
      ∗ ∀ (i : Nat) (h : i < rem.size) (pa : Addr),
        ba.id ↦ cell ∗ pa.id ↦ (⟨some keyTy, (rem[i]'h).1⟩ : HeapCell) -∗
        WP (Config.exec body (env.pushScope.declare kid (.base pa))
              (.mapIterK (some kid) none keyTy valTy body (some (.base ba))
                (produced.push (rem[i]'h).1) start env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.next (.mapIterK (some kid) none keyTy valTy body
            (some (.base ba)) produced start env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hcell, Hcont⟩
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
  ihave %Hmap : ⌜get? (heapToMap σ₁.heap) ba.id = some cell⌝ $$ [Hσ Hcell]
  · icases genHeap_valid $$ [$Hσ $Hcell] with >%h
    itrivial
  have hlook : Heap.lookup σ₁.heap (.base ba) = some cell := by
    rw [get?_heapToMap] at Hmap; simpa using Hmap
  have hc := hcands σ₁ htypes hlook
  have hm := hmand σ₁ htypes hlook
  have hsnap := mapIterCandidates_normalized hc
  have hbind : ∀ (i : Nat) (h : i < rem.size),
      bindIterVars env.pushScope σ₁ (some kid) none keyTy valTy
        ((rem[i]'h).1) ((rem[i]'h).2)
      = .ok (env.pushScope.declare kid (.base ⟨σ₁.nextAddr⟩),
          { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩)
                      ⟨some keyTy, (rem[i]'h).1⟩,
                    nextAddr := σ₁.nextAddr + 1 }) := by
    intro i h
    have hmem := snapshotEntriesSelfNormalizedList_mem
      (types := σ₁.types) (kt := keyTy) (vt := valTy)
      (l := rem.toList) hsnap (e := rem[i]'h)
      (List.mem_of_getElem? (by
        rw [Array.getElem?_toList]
        exact Array.getElem?_eq_getElem h))
    exact bindIterVars_key_only (isNormalForTy_sound hmem.1)
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], _, _, [],
        GoPrimStep.step (Step.mapIterNext (idx := 0) hne hc hm (hbind 0 hne))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    cases st with
    | mapIterDone hcands' =>
        rw [hc] at hcands'
        injection hcands' with hcands'
        exact absurd hne (by rw [hcands']; simp)
    | mapIterStop hcands' _ hmand' =>
        rw [hc] at hcands'
        injection hcands' with hcands'
        rw [← hcands'] at hmand'
        rw [hm] at hmand'
        injection hmand' with hmand'
        cases hmand'
    | @mapIterNext _ _ _ _ _ _ _ _ cands' _ idx _ env' _ _ s' hidx hcands' hmand' hbindStep =>
      rw [hc] at hcands'
      injection hcands' with hcands'
      subst hcands'
      rw [hbind idx hidx] at hbindStep
      injection hbindStep with h1
      obtain ⟨henv, hst⟩ := Prod.mk.inj h1
      subst henv
      subst hst
      imod (genHeap_alloc
        (v := (⟨some keyTy, (rem[idx]'hidx).1⟩ : HeapCell))
        hwf.fresh_get?) $$ Hσ with ⟨Hσ, Hpt, Htok⟩
      imod Hclose
      imodintro
      simp only [Algebra.BigOpL.bigOpL_nil]
      isplitl [Hσ]
      · isplitl [Hσ]
        · iapply (genHeapInterp_eqv
            (fun kk => (heapToMap_set_base σ₁.heap ⟨σ₁.nextAddr⟩ _ kk).symm)) $$ Hσ
        · ipureintro
          exact ⟨hfns, hmeths, htypes, hwf.alloc⟩
      · isplitl [Hpt Hcell Hcont]
        · iapply Hcont $$ %idx %hidx %(⟨σ₁.nextAddr⟩ : Addr)
          isplitl [Hcell]
          · iexact Hcell
          · iexact Hpt
        · itrivial

/-! ## Non-vacuity witnesses for `wp_map_iter_next_key`

CLAUDE.md's gate: a user-facing WP law ships with a theorem that
instantiates it on a concrete program and discharges every premise but
the genuinely-external ones. Under the (L) surgery the witnesses run
against an OWNED CELL (the pick loads live), so each fixes a concrete
cell content and computes the pick-time facts against it. Two
witnesses, one per side of the `σ.types`-pin gap:

* `..._basic_key_witness` — a `uint64` key, where the comparator and
  the validation never touch `σ.types` and the pin rides unused;
* `..._defined_key_witness` — a DEFINED key type, UNINSTANTIABLE
  without the pin: both the candidates validation and the produced-set
  comparator resolve the name through `TypeEnv.lookup σ.types`.

Neither witness names the pilot target (standing over-specialization
check). -/

/-- A one-entry cell: enough to make `hne` true and force the premise
quantifiers to be discharged at a real index. Under (L) the VALUE must
also validate at the (now concrete) value type — `.int 0 .uint64`. -/
private def witnessEntries : Array (GoValue × GoValue) :=
  #[(.int 7 .uint64, .int 0 .uint64)]

/-- A DEFINED key type's name. Deliberately NOT one of the pilot's
(`main.Index`): the witness must exercise the language capability, not the
target (standing over-specialization check, 2026-07-31). -/
private def witnessKeyName : TypeId := ⟨"pkg.Key"⟩

private theorem witnessEntries_index_zero {i : Nat} (h : i < witnessEntries.size) :
    i = 0 :=
  Nat.lt_one_iff.mp (by simpa [witnessEntries] using h)

/-- **Witness at a BASIC key type.** -/
theorem wp_map_iter_next_key_basic_key_witness {kid : String}
    {body : Stmt} {ba : Addr} {mty : Option Ty} {env k} :
    iprop(ba.id ↦ (⟨mty, .mapData witnessEntries⟩ : HeapCell)
      ∗ ∀ (i : Nat) (h : i < witnessEntries.size) (pa : Addr),
        ba.id ↦ (⟨mty, .mapData witnessEntries⟩ : HeapCell)
          ∗ pa.id ↦ (⟨some (.int .uint64), (witnessEntries[i]'h).1⟩ : HeapCell) -∗
        WP (Config.exec body (env.pushScope.declare kid (.base pa))
              (.mapIterK (some kid) none (.int .uint64) (.int .uint64) body
                (some (.base ba)) (#[].push (witnessEntries[i]'h).1)
                (witnessEntries.map (·.1)) env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.next (.mapIterK (some kid) none (.int .uint64) (.int .uint64)
            body (some (.base ba)) #[] (witnessEntries.map (·.1)) env k))
          @ s ; E {{ Φ }} :=
  wp_map_iter_next_key (by decide)
    (fun σ _htypes hlook => by
      simp +decide [mapIterCandidates, mapIterLiveEntries, loadLoc, hlook,
        witnessEntries, filterCandidateList, keyInKeys, keyInKeyList,
        snapshotEntriesSelfNormalized, snapshotEntriesSelfNormalizedList,
        isNormalForTy, isNormalForTyFuel, typeResolutionFuel,
        Bind.bind, Except.bind, pure, Except.pure])
    (fun σ _htypes hlook => by
      simp [mapIterMandatoryRemains, mandatoryInList, keyInKeys,
        keyInKeyList, witnessEntries, valueEq, valueEqFuel,
        typeResolutionFuel, Bind.bind, Except.bind, pure, Except.pure])

/-- **Witness at a DEFINED key type — the instance the unpinned facts
could not have.** Both computations resolve `pkg.Key` through the
pinned type environment; drop `htypes` and no proof exists. -/
theorem wp_map_iter_next_key_defined_key_witness {kid : String}
    {body : Stmt} {ba : Addr} {mty : Option Ty} {env k}
    (htypes : GoCoreGS.types GF = [(witnessKeyName, TypeDef.defined (.int .uint64))]) :
    iprop(ba.id ↦ (⟨mty, .mapData witnessEntries⟩ : HeapCell)
      ∗ ∀ (i : Nat) (h : i < witnessEntries.size) (pa : Addr),
        ba.id ↦ (⟨mty, .mapData witnessEntries⟩ : HeapCell)
          ∗ pa.id ↦ (⟨some (.defined witnessKeyName), (witnessEntries[i]'h).1⟩ : HeapCell) -∗
        WP (Config.exec body (env.pushScope.declare kid (.base pa))
              (.mapIterK (some kid) none (.defined witnessKeyName) (.int .uint64) body
                (some (.base ba)) (#[].push (witnessEntries[i]'h).1)
                (witnessEntries.map (·.1)) env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.next (.mapIterK (some kid) none (.defined witnessKeyName)
            (.int .uint64) body (some (.base ba)) #[]
            (witnessEntries.map (·.1)) env k))
          @ s ; E {{ Φ }} :=
  wp_map_iter_next_key (by decide)
    (fun σ hσ hlook => by
      have hty : σ.types = [(witnessKeyName, TypeDef.defined (.int .uint64))] := by
        rw [hσ, htypes]
      simp +decide [mapIterCandidates, mapIterLiveEntries, loadLoc, hlook,
        witnessEntries, filterCandidateList, keyInKeys, keyInKeyList,
        snapshotEntriesSelfNormalized, snapshotEntriesSelfNormalizedList,
        isNormalForTy, isNormalForTyFuel, typeResolutionFuel, hty,
        TypeEnv.lookup, witnessKeyName,
        Bind.bind, Except.bind, pure, Except.pure])
    (fun σ hσ hlook => by
      have hty : σ.types = [(witnessKeyName, TypeDef.defined (.int .uint64))] := by
        rw [hσ, htypes]
      simp [mapIterMandatoryRemains, mandatoryInList, keyInKeys,
        keyInKeyList, witnessEntries, valueEq, valueEqFuel,
        typeResolutionFuel, hty, TypeEnv.lookup, witnessKeyName,
        Bind.bind, Except.bind, pure, Except.pure])

/-! ## THE INDUCTIVE RANGE RULE, (L) form

One generic-iteration obligation over an arbitrary remaining candidate
set and an arbitrary pick, plus the invariant at entry and exit — the
k!-collapse rule, now against the OWNED live cell. The iteration
bookkeeping is the caller's REACHABLE-STATE relation `P produced rem`
(the produced set and the candidates it leaves), with three facts:
`hfact` computes the machine's pick-time candidates/mandatory against
the owned cell at every reachable state; `hstep` closes `P` under a
pick; `hP0` seeds it. The mutation-free contract is visible in the
shapes: the cell rides through unchanged (the LAW holds it across the
body — `Hbody` never sees it, so `I` stays a function of the
candidates alone, exactly the old interface), and `hfact`'s
`mandatory = true` is what a body that deletes from the ranged map
could not supply. Scope (recorded): key-only, normally-completing
bodies, mutation-free ranges — the stop-admitting and mutating forms
land with the first walk that needs them (kit obligation, arc log). -/
theorem wp_map_iter_inv {kid : String} {keyTy valTy : Ty} {body : Stmt}
    {ba : Addr} {cell : HeapCell}
    {start : Array GoValue} {env k}
    {P : Array GoValue → Array (GoValue × GoValue) → Prop}
    {produced0 : Array GoValue} {entries0 : Array (GoValue × GoValue)}
    {I : Array (GoValue × GoValue) → IProp GF}
    (hP0 : P produced0 entries0)
    (hfact : ∀ pr rem, P pr rem → ∀ (σ : ExecState),
      σ.types = GoCoreGS.types GF →
      Heap.lookup σ.heap (.base ba) = some cell →
      mapIterCandidates σ keyTy valTy (some (.base ba)) pr = .ok rem
        ∧ (0 < rem.size →
            mapIterMandatoryRemains σ keyTy rem start = .ok true))
    (hstep : ∀ pr rem (i : Nat) (h : i < rem.size), P pr rem →
      P (pr.push (rem[i]'h).1) (rem.eraseIdx i h))
    (Hbody : ∀ pr rem (i : Nat) (h : i < rem.size) (pa : Addr), P pr rem →
      iprop(I rem
        ∗ pa.id ↦ (⟨some keyTy, (rem[i]'h).1⟩ : HeapCell)
        ∗ (I (rem.eraseIdx i h) -∗
            WP (Config.next (.mapIterK (some kid) none keyTy valTy body
                  (some (.base ba)) (pr.push (rem[i]'h).1) start env k))
              @ s ; E {{ Φ }}))
      ⊢ WP (Config.exec body (env.pushScope.declare kid (.base pa))
              (.mapIterK (some kid) none keyTy valTy body
                (some (.base ba)) (pr.push (rem[i]'h).1) start env k))
          @ s ; E {{ Φ }}) :
    iprop(ba.id ↦ cell ∗ I entries0
        ∗ (I #[] ∗ ba.id ↦ cell -∗ WP (Config.next k) @ s ; E {{ Φ }}))
      ⊢ WP (Config.next (.mapIterK (some kid) none keyTy valTy body
            (some (.base ba)) produced0 start env k)) @ s ; E {{ Φ }} := by
  suffices hgen : ∀ (n : Nat) (pr : Array GoValue)
      (rem : Array (GoValue × GoValue)), rem.size ≤ n → P pr rem →
      iprop(ba.id ↦ cell ∗ I rem
          ∗ (I #[] ∗ ba.id ↦ cell -∗ WP (Config.next k) @ s ; E {{ Φ }}))
        ⊢ WP (Config.next (.mapIterK (some kid) none keyTy valTy body
              (some (.base ba)) pr start env k)) @ s ; E {{ Φ }} from
    hgen entries0.size produced0 entries0 (Nat.le_refl _) hP0
  intro n
  induction n with
  | zero =>
    intro pr rem hsz hP
    obtain rfl : rem = #[] := Array.eq_empty_of_size_eq_zero (Nat.le_zero.mp hsz)
    iintro ⟨Hcell, HI, Hexit⟩
    iapply (wp_map_iter_done
      (hcands := fun σ hσ hlook => (hfact pr #[] hP σ hσ hlook).1))
    isplitl [Hcell]
    · iexact Hcell
    iintro Hcell
    iapply Hexit
    isplitl [HI]
    · iexact HI
    · iexact Hcell
  | succ n ih =>
    intro pr rem hsz hP
    rcases Nat.eq_zero_or_pos rem.size with h0 | hne
    · obtain rfl : rem = #[] := Array.eq_empty_of_size_eq_zero h0
      iintro ⟨Hcell, HI, Hexit⟩
      iapply (wp_map_iter_done
        (hcands := fun σ hσ hlook => (hfact pr #[] hP σ hσ hlook).1))
      isplitl [Hcell]
      · iexact Hcell
      iintro Hcell
      iapply Hexit
      isplitl [HI]
      · iexact HI
      · iexact Hcell
    · iintro ⟨Hcell, HI, Hexit⟩
      iapply (wp_map_iter_next_key (hne := hne)
        (hcands := fun σ hσ hlook => (hfact pr rem hP σ hσ hlook).1)
        (hmand := fun σ hσ hlook => (hfact pr rem hP σ hσ hlook).2 hne))
      isplitl [Hcell]
      · iexact Hcell
      iintro %i %h %pa ⟨Hcell, Hpt⟩
      iapply (Hbody pr rem i h pa hP)
      isplitl [HI]
      · iexact HI
      isplitl [Hpt]
      · iexact Hpt
      iintro HI'
      iapply (ih (pr.push (rem[i]'h).1) (rem.eraseIdx i h)
        (by rw [Array.size_eraseIdx]; omega)
        (hstep pr rem i h hP))
      isplitl [Hcell]
      · iexact Hcell
      isplitl [HI']
      · iexact HI'
      · iexact Hexit

/-! ### Witness for `wp_map_iter_inv` — a NON-QUORUM program

`for k := range m { sum = sum + k }` (corpus case
`range/range-map-key-sum`) at a CONCRETE two-key cell. HONESTY NOTE
(recorded, kit obligation in the arc log): the pre-(L) witness ran over
an ARBITRARY snapshot of nonnegative int keys; under (L) the pick-time
facts are semantic-comparator computations against the owned cell, and
the generic abstract-key candidate algebra that would restore the
arbitrary-snapshot witness is owed to the kit (MapMem carries its
uint64 list-model instance). The witness still discharges EVERY
premise of the rule on a real program shape — including a genuinely
order-branching two-key range (both pick orders are walked by the ONE
generic-iteration obligation) — which is what the non-vacuity gate
demands. The body statement is a HAND-BUILT GoCore term, as before. -/

/-- The witness body: `sum = sum + k`, the loop body of
`range/range-map-key-sum`. -/
def keySumBody : Stmt := .assign (.var "sum") (.add (.var "sum") (.var "k"))

/-- The witness's cell: keys 3 and 4 (values unused by the body). -/
private def ksEntries : Array (GoValue × GoValue) :=
  #[(.int 3 .int, .int 0 .int), (.int 4 .int, .int 0 .int)]

private def ksE4 : Array (GoValue × GoValue) := #[(.int 4 .int, .int 0 .int)]
private def ksE3 : Array (GoValue × GoValue) := #[(.int 3 .int, .int 0 .int)]

/-- The reachable iteration states of the witness range. -/
private inductive KsP : Array GoValue → Array (GoValue × GoValue) → Prop
  | start : KsP #[] ksEntries
  | after3 : KsP #[.int 3 .int] ksE4
  | after4 : KsP #[.int 4 .int] ksE3
  | done34 : KsP #[.int 3 .int, .int 4 .int] #[]
  | done43 : KsP #[.int 4 .int, .int 3 .int] #[]

/-- The fold the witness's invariant tracks. -/
def keyInt : GoValue → Int
  | .int n _ => n
  | _ => 0

def keyIntSum (a : Array (GoValue × GoValue)) : Int :=
  (a.toList.map (fun p => keyInt p.1)).sum

/-- `int` is 64-bit two's complement; a nonnegative value below `2^63`
rides through `IntKind.normalize` unchanged. -/
theorem int_normalize_of_nonneg_lt {v : Int} (h0 : 0 ≤ v) (h1 : v < 2 ^ 63) :
    IntKind.int.normalize v = v := by
  have hmod : v % (2 : Int) ^ 64 = v := Int.emod_eq_of_lt h0 (by omega)
  simp only [IntKind.normalize, IntKind.bits?, IntKind.signed, hmod, if_true,
    if_neg (show ¬ (v ≥ (2 : Int) ^ (64 - 1)) by omega)]

/-- **WITNESS: `for k := range m { sum = sum + k }` at the two-key
cell.** Both pick orders are covered by the one generic-iteration
obligation; `sum` ends at 7 either way. -/
theorem wp_map_iter_inv_key_sum_witness {acc ba : Addr} {mty : Option Ty}
    {env k}
    (hacc : LocalEnv.lookup env "sum" = some (.base acc)) :
    iprop(ba.id ↦ (⟨mty, .mapData ksEntries⟩ : HeapCell)
      ∗ acc.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ∗ ((acc.id ↦ (⟨some (.int .int), .int 7 .int⟩ : HeapCell)
          ∗ ba.id ↦ (⟨mty, .mapData ksEntries⟩ : HeapCell))
          -∗ WP (Config.next k) @ s ; E {{ Φ }}))
      ⊢ WP (Config.next (.mapIterK (some "k") none (.int .int) (.int .int)
            keySumBody (some (.base ba)) #[] (ksEntries.map (·.1)) env k))
          @ s ; E {{ Φ }} := by
  iintro ⟨Hcell, Hacc, Hexit⟩
  iapply (wp_map_iter_inv (P := KsP)
    (cell := (⟨mty, .mapData ksEntries⟩ : HeapCell))
    (I := fun rem => iprop(∃ v : Int,
      ⌜v = 7 - keyIntSum rem ∧ (rem = ksEntries ∨ rem = ksE4 ∨ rem = ksE3 ∨ rem = #[])⌝
        ∗ acc.id ↦ (⟨some (.int .int), .int v .int⟩ : HeapCell)))
    (hP0 := KsP.start)
    (hfact := by
      intro pr rem hP σ hσ hlook
      cases hP
      case start => exact ⟨by
          simp +decide [mapIterCandidates, mapIterLiveEntries, loadLoc, hlook,
            ksEntries, ksE3, ksE4, filterCandidateList, keyInKeys,
            keyInKeyList, valueEq, valueEqFuel, typeResolutionFuel,
            snapshotEntriesSelfNormalized, snapshotEntriesSelfNormalizedList,
            isNormalForTy, isNormalForTyFuel,
            Bind.bind, Except.bind, pure, Except.pure], fun hne => by
          simp +decide [mapIterMandatoryRemains, mandatoryInList, keyInKeys,
            keyInKeyList, ksEntries, ksE3, ksE4, valueEq, valueEqFuel,
            typeResolutionFuel, Bind.bind, Except.bind, pure, Except.pure]⟩
      case after3 => exact ⟨by
          simp +decide [mapIterCandidates, mapIterLiveEntries, loadLoc, hlook,
            ksEntries, ksE3, ksE4, filterCandidateList, keyInKeys,
            keyInKeyList, valueEq, valueEqFuel, typeResolutionFuel,
            snapshotEntriesSelfNormalized, snapshotEntriesSelfNormalizedList,
            isNormalForTy, isNormalForTyFuel,
            Bind.bind, Except.bind, pure, Except.pure], fun hne => by
          simp +decide [mapIterMandatoryRemains, mandatoryInList, keyInKeys,
            keyInKeyList, ksEntries, ksE3, ksE4, valueEq, valueEqFuel,
            typeResolutionFuel, Bind.bind, Except.bind, pure, Except.pure]⟩
      case after4 => exact ⟨by
          simp +decide [mapIterCandidates, mapIterLiveEntries, loadLoc, hlook,
            ksEntries, ksE3, ksE4, filterCandidateList, keyInKeys,
            keyInKeyList, valueEq, valueEqFuel, typeResolutionFuel,
            snapshotEntriesSelfNormalized, snapshotEntriesSelfNormalizedList,
            isNormalForTy, isNormalForTyFuel,
            Bind.bind, Except.bind, pure, Except.pure], fun hne => by
          simp +decide [mapIterMandatoryRemains, mandatoryInList, keyInKeys,
            keyInKeyList, ksEntries, ksE3, ksE4, valueEq, valueEqFuel,
            typeResolutionFuel, Bind.bind, Except.bind, pure, Except.pure]⟩
      case done34 => exact ⟨by
          simp +decide [mapIterCandidates, mapIterLiveEntries, loadLoc, hlook,
            ksEntries, ksE3, ksE4, filterCandidateList, keyInKeys,
            keyInKeyList, valueEq, valueEqFuel, typeResolutionFuel,
            snapshotEntriesSelfNormalized, snapshotEntriesSelfNormalizedList,
            isNormalForTy, isNormalForTyFuel,
            Bind.bind, Except.bind, pure, Except.pure], fun hne => absurd hne (by simp)⟩
      case done43 => exact ⟨by
          simp +decide [mapIterCandidates, mapIterLiveEntries, loadLoc, hlook,
            ksEntries, ksE3, ksE4, filterCandidateList, keyInKeys,
            keyInKeyList, valueEq, valueEqFuel, typeResolutionFuel,
            snapshotEntriesSelfNormalized, snapshotEntriesSelfNormalizedList,
            isNormalForTy, isNormalForTyFuel,
            Bind.bind, Except.bind, pure, Except.pure], fun hne => absurd hne (by simp)⟩)
    (hstep := by
      intro pr rem i h hP
      cases hP with
      | start =>
          match i, h with
          | 0, h => exact (by simpa [ksEntries, ksE4] using KsP.after3)
          | 1, h => exact (by simpa [ksEntries, ksE3] using KsP.after4)
      | after3 =>
          match i, h with
          | 0, h => exact (by simpa [ksE4] using KsP.done34)
      | after4 =>
          match i, h with
          | 0, h => exact (by simpa [ksE3] using KsP.done43)
      | done34 => exact absurd h (by simp)
      | done43 => exact absurd h (by simp))
    (Hbody := by
      intro pr rem i h pa hP
      iintro ⟨⟨%v, %hv, Hacc⟩, Hkey, Hk⟩
      obtain ⟨hv0, hshape⟩ := hv
      -- the picked key's payload and the post-pick fold, by shape
      have hkey : ∃ m : Int, (rem[i]'h).1 = .int m .int
          ∧ keyIntSum (rem.eraseIdx i h) = keyIntSum rem - m
          ∧ 0 ≤ v + m ∧ v + m < 2 ^ 63 := by
        rcases hshape with rfl | rfl | rfl | rfl
        · have hv' : v = 0 := by
            simpa [ksEntries, keyIntSum, keyInt] using hv0
          match i, h with
          | 0, h =>
              exact ⟨3, rfl, by simp [ksEntries, keyIntSum, keyInt],
                by omega, by omega⟩
          | 1, h =>
              exact ⟨4, rfl, by simp [ksEntries, keyIntSum, keyInt],
                by omega, by omega⟩
        · have hv' : v = 3 := by
            simpa [ksE4, keyIntSum, keyInt] using hv0
          match i, h with
          | 0, h =>
              exact ⟨4, rfl, by simp [ksE4, keyIntSum, keyInt],
                by omega, by omega⟩
        · have hv' : v = 4 := by
            simpa [ksE3, keyIntSum, keyInt] using hv0
          match i, h with
          | 0, h =>
              exact ⟨3, rfl, by simp [ksE3, keyIntSum, keyInt],
                by omega, by omega⟩
        · exact absurd h (by simp)
      obtain ⟨m, hm, herase, hlo, hhi⟩ := hkey
      have hshape' : rem.eraseIdx i h = ksEntries ∨ rem.eraseIdx i h = ksE4
          ∨ rem.eraseIdx i h = ksE3 ∨ rem.eraseIdx i h = #[] := by
        rcases hshape with rfl | rfl | rfl | rfl
        · match i, h with
          | 0, h => simp [ksEntries, ksE4]
          | 1, h => simp [ksEntries, ksE3]
        · match i, h with
          | 0, h => simp [ksE4]
        · match i, h with
          | 0, h => simp [ksE3]
        · exact absurd h (by simp)
      rw [hm]
      -- `sum = sum + k`
      unfold keySumBody
      iapply (wp_assign_start (e := .ref "sum") (sh := .chain []) (ops := []) rfl)
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hc₁
      iapply (wp_eval_ref (loc := Loc.base acc)
        (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
          Scope.lookup, hacc]))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hc₂
      iapply (wp_tgtop_rhs rfl)
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hc₃
      iapply (wp_eval_strict (op := .add) (e₁ := .var "sum")
        (rest := [.var "k"]) rfl)
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hc₄
      iapply (wp_eval_var (a := acc) (cell := ⟨some (.int .int), .int v .int⟩)
        (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
          Scope.lookup, hacc]))
      isplitl [Hacc]
      · iexact Hacc
      iintro Hacc
      iapply wp_strict_shift
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hc₅
      iapply (wp_eval_var (a := pa) (cell := ⟨some (.int .int), .int m .int⟩)
        (by simp [LocalEnv.lookup, LocalEnv.declare, LocalEnv.pushScope,
          Scope.lookup]))
      isplitl [Hkey]
      · iexact Hkey
      iintro Hkey
      iapply (wp_strict_apply_pure (out := .int (v + m) .int) (happly := by
        intro σ
        simp [applyStrictOp, intBinaryResult, valueAsIntValue,
          show IntKind.compatibleResult .int .int = some .int from rfl,
          int_normalize_of_nonneg_lt hlo hhi, Bind.bind, Except.bind]))
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hc₆
      iapply wp_rhs_stores_vals
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro Hc₇
      simp only [List.nil_append, List.reverse_cons, List.reverse_nil]
      iapply (wp_assign_store
        (oldcell := ⟨some (.int .int), .int v .int⟩)
        (newcell := ⟨some (.int .int), .int (v + m) .int⟩)
        (hstore := fun σ _ht hlook => by
          have hst := storeLoc_int_any (mkind := .int) hlook (v + m)
          rw [int_normalize_of_nonneg_lt hlo hhi] at hst
          exact hst))
      isplitl [Hacc]
      · iexact Hacc
      iintro Hacc
      iapply wp_stores_done_nil
      iapply Hk
      iexists (v + m)
      isplitl []
      · ipureintro
        exact ⟨by omega, hshape'⟩
      · iexact Hacc))
  isplitl [Hcell]
  · iexact Hcell
  isplitl [Hacc]
  · iexists (0 : Int)
    isplitl []
    · ipureintro
      refine ⟨by simp [ksEntries, keyIntSum, keyInt], Or.inl rfl⟩
    · iexact Hacc
  · iintro ⟨⟨%v, %hv, Hacc⟩, Hcell⟩
    obtain ⟨hv0, -⟩ := hv
    have : v = 7 := by simpa [keyIntSum] using hv0
    subst this
    iapply Hexit
    isplitl [Hacc]
    · iexact Hacc
    · iexact Hcell

end

end GoLean.Iris