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

/-- Deterministic despite the conservative `choiceFree`: an exhausted
snapshot pops the iteration context (`mapIterNext` needs an index below
zero to fire here). -/
theorem wp_map_iter_done {kid : Option String} {vv : Option String}
    {keyTy valTy : Ty} {body : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗ WP (Config.next k) @ s ; E {{ Φ }}) ⊢
      WP (Config.next (.mapIterK kid vv keyTy valTy body #[] env k))
        @ s ; E {{ Φ }} :=
  wp_pure_det' rfl (fun _ => Step.mapIterDone)
    (fun σ c' σ' hst => by
      cases hst with
      | mapIterDone => exact ⟨rfl, rfl⟩
      | mapIterNext hidx _ => exact absurd hidx (by simp))

/-- Dispatch a map range: evaluate the map expression. -/
theorem wp_map_range_start {keyVar valVar : Option String}
    {mapExpr : Expr} {keyTy valTy : Ty} {body : Stmt} {env k} :
    (|={E}[E]▷=> £ 1 -∗
      WP (Config.evalE mapExpr env
        (.mapRangeK keyVar valVar keyTy valTy body env k)) @ s ; E {{ Φ }}) ⊢
      WP (Config.exec (.mapRange keyVar valVar mapExpr keyTy valTy body) env k)
        @ s ; E {{ Φ }} :=
  wp_pure_det rfl (by simp [Config.choiceFree, stmtPlan])
    (fun _ => Step.mapRange)

/-- **THE NONDETERMINISTIC STEP, key-only form**: from a NONEMPTY
snapshot, the machine picks ANY index `i` and allocates the key cell at
a machine-chosen address. The premise supplies the continuation for
EVERY such choice (`∀ i pa`); safety is witnessed at `i = 0`. `hnorm`
asks the keys to normalize to themselves at the range key type — true of
the already-normalized values a map snapshot holds.

`hnorm` carries the `σ.types` GHOST PIN, exactly like `wp_init`,
`wp_strict_apply_pin` and the `stmtOpK` apply cores. Without it the
premise quantifies over ALL states, and `normalizeValueForTy` resolves a
`.defined` key type through `TypeEnv.lookup σ.types` — so at a NAMED key
type (`map[Index]bool`, `map[NodeID]struct{}`, the ordinary raft shape)
the unpinned premise is FALSE for the hostile `σ` with an empty type
env, and the law would be VACUOUS there while looking general (pre-merge
audit 2026-07-31, finding 9; `Ghost.lean`'s rule, demonstrated by
`Laws/QuorumOps.typeEnv_pin_is_load_bearing`). At a BASIC key type the
pin is simply unused, so `fun _ _ i h => by simp …` still discharges it.
Witnesses: `wp_map_iter_next_key_basic_key_witness` (basic key) and
`wp_map_iter_next_key_defined_key_witness` (DEFINED key — the instance
the unpinned form could not have). -/
theorem wp_map_iter_next_key {kid : String} {keyTy valTy : Ty}
    {body : Stmt} {remaining : Array (GoValue × GoValue)} {env k}
    (hne : 0 < remaining.size)
    (hnorm : ∀ (σ : ExecState), σ.types = GoCoreGS.types GF →
      ∀ (i : Nat) (h : i < remaining.size),
      normalizeValueForTy σ keyTy ((remaining[i]'h).1) = .ok ((remaining[i]'h).1)) :
    iprop(∀ (i : Nat) (h : i < remaining.size) (pa : Addr),
        pa.id ↦ (⟨some keyTy, (remaining[i]'h).1⟩ : HeapCell) -∗
        WP (Config.exec body (env.pushScope.declare kid (.base pa))
              (.mapIterK (some kid) none keyTy valTy body
                (remaining.eraseIdx i h) env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.next (.mapIterK (some kid) none keyTy valTy body remaining env k))
          @ s ; E {{ Φ }} := by
  iintro Hcont
  iapply wp_lift_step (h := rfl)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  simp only [stateInterp]
  icases Hσ with ⟨Hσ, %Hinv⟩
  obtain ⟨hfns, hmeths, htypes, hwf⟩ := Hinv
  have hbind : ∀ (i : Nat) (h : i < remaining.size),
      bindIterVars env.pushScope σ₁ (some kid) none keyTy valTy
        ((remaining[i]'h).1) ((remaining[i]'h).2)
      = .ok (env.pushScope.declare kid (.base ⟨σ₁.nextAddr⟩),
          { σ₁ with heap := Heap.set σ₁.heap (.base ⟨σ₁.nextAddr⟩)
                      ⟨some keyTy, (remaining[i]'h).1⟩,
                    nextAddr := σ₁.nextAddr + 1 }) :=
    fun i h => bindIterVars_key_only (hnorm σ₁ htypes i h)
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact ⟨[], _, _, [],
        GoPrimStep.step (Step.mapIterNext (idx := 0) hne (hbind 0 hne))⟩
    · trivial
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  cases Hstep with
  | step st =>
    cases st with
    | mapIterDone => exact absurd hne (by simp)
    | @mapIterNext _ _ _ _ _ _ idx _ env' _ _ s' hidx hbindStep =>
      rw [hbind idx hidx] at hbindStep
      injection hbindStep with h1
      obtain ⟨henv, hst⟩ := Prod.mk.inj h1
      subst henv
      subst hst
      imod (genHeap_alloc
        (v := (⟨some keyTy, (remaining[idx]'hidx).1⟩ : HeapCell))
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
      · isplitl [Hpt Hcont]
        · iapply Hcont $$ %idx %hidx %(⟨σ₁.nextAddr⟩ : Addr) Hpt
        · itrivial

/-! ## Non-vacuity witnesses for `wp_map_iter_next_key`

CLAUDE.md's gate: a user-facing WP law ships with a theorem that
instantiates it on a concrete program and discharges every premise but
the genuinely-external ones. `wp_map_iter_next_key` shipped without one
(2528b4f), and the missing witness is exactly what hid the `hnorm`
vacuity at named key types (pre-merge audit 2026-07-31, finding 9). Two
witnesses, one per side of the gap:

* `..._basic_key_witness` — a `uint64` key, where `hnorm` never touches
  `σ.types` and the pin rides unused;
* `..._defined_key_witness` — a DEFINED key type (`map[K]…` for a named
  `K`, the ordinary Go shape), which is UNINSTANTIABLE without the pin:
  `normalizeValueForTy` resolves the name through `TypeEnv.lookup
  σ.types` and fails closed on a miss, so the old `∀σ` premise was FALSE
  there. Its type-env hypothesis is external in the same sense as every
  `htypes` in `Specs/` — a fact about the program under proof — and it is
  SATISFIABLE, which the vacuous premise was not.

Neither witness names the pilot target: both are stated for an arbitrary
`TypeId` and an arbitrary continuation. -/

/-- A one-entry snapshot: enough to make `hne` true and force `hnorm`'s
`∀ i` to be discharged at a real index. -/
private def witnessSnapshot : Array (GoValue × GoValue) :=
  #[(.int 7 .uint64, .nil)]

/-- A DEFINED key type's name. Deliberately NOT one of the pilot's
(`main.Index`): the witness must exercise the language capability, not the
target (standing over-specialization check, 2026-07-31). -/
private def witnessKeyName : TypeId := ⟨"pkg.Key"⟩

private theorem witnessSnapshot_index_zero {i : Nat} (h : i < witnessSnapshot.size) :
    i = 0 :=
  Nat.lt_one_iff.mp (by simpa [witnessSnapshot] using h)

/-- **Witness at a BASIC key type.** `hnorm` is state-independent here, so
the pin is supplied and unused — the law is no weaker than before at the
key types the pilot's own walk uses. -/
theorem wp_map_iter_next_key_basic_key_witness {kid : String}
    {valTy : Ty} {body : Stmt} {env k} :
    iprop(∀ (i : Nat) (h : i < witnessSnapshot.size) (pa : Addr),
        pa.id ↦ (⟨some (.int .uint64), (witnessSnapshot[i]'h).1⟩ : HeapCell) -∗
        WP (Config.exec body (env.pushScope.declare kid (.base pa))
              (.mapIterK (some kid) none (.int .uint64) valTy body
                (witnessSnapshot.eraseIdx i h) env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.next (.mapIterK (some kid) none (.int .uint64) valTy body
              witnessSnapshot env k)) @ s ; E {{ Φ }} :=
  wp_map_iter_next_key (by decide)
    (fun _σ _htypes i h => by
      obtain rfl := witnessSnapshot_index_zero h
      simp [witnessSnapshot, normalizeValueForTy, normalizeValueForTyFuel,
        show IntKind.uint64.normalize 7 = 7 from by decide])

/-- **Witness at a DEFINED key type — the instance the unpinned law did
not have.** `hnorm` is discharged only BECAUSE the pin lets it read the
program's type environment; drop `htypes` and no proof exists, since the
premise is refutable at `σ.types = []`. -/
theorem wp_map_iter_next_key_defined_key_witness {kid : String}
    {valTy : Ty} {body : Stmt} {env k}
    (htypes : GoCoreGS.types GF = [(witnessKeyName, TypeDef.defined (.int .uint64))]) :
    iprop(∀ (i : Nat) (h : i < witnessSnapshot.size) (pa : Addr),
        pa.id ↦ (⟨some (.defined witnessKeyName), (witnessSnapshot[i]'h).1⟩ : HeapCell) -∗
        WP (Config.exec body (env.pushScope.declare kid (.base pa))
              (.mapIterK (some kid) none (.defined witnessKeyName) valTy body
                (witnessSnapshot.eraseIdx i h) env k)) @ s ; E {{ Φ }})
      ⊢ WP (Config.next (.mapIterK (some kid) none (.defined witnessKeyName) valTy body
              witnessSnapshot env k)) @ s ; E {{ Φ }} :=
  wp_map_iter_next_key (by decide)
    (fun σ hσ i h => by
      obtain rfl := witnessSnapshot_index_zero h
      have hty : σ.types = [(witnessKeyName, TypeDef.defined (.int .uint64))] := by
        rw [hσ, htypes]
      simp +decide [witnessSnapshot, witnessKeyName, normalizeValueForTy,
        normalizeValueForTyFuel, hty, TypeEnv.lookup, typeResolutionFuel,
        show IntKind.uint64.normalize 7 = 7 from by decide])

end

end GoLean.Iris
