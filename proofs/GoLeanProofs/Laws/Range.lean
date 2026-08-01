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

/-- Deterministic despite the conservative `choiceFree`: an exhausted
snapshot pops the iteration context (`mapIterNext` needs an index below
zero to fire here). -/
@[go_walk_law]
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
`Specs/GoldenQuorumPin.typeEnv_pin_is_load_bearing`). At a BASIC key type the
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

/-! ## THE INDUCTIVE RANGE RULE (proof-automation arc phase 1, 2026-08-01)

`wp_map_iter_next_key` discharges ONE iteration and leaves a WP over the
shrunk snapshot; a k-entry range walked with it alone costs k! branches
(one per pick order), which is why the n = 1 summit could be walked by
hand and n = 3 could not. `wp_map_iter_inv` is the loop-invariant rule
that collapses that: ONE generic-iteration obligation over an arbitrary
remaining snapshot and an arbitrary pick, plus the invariant at entry
and exit.

It is the NONDETERMINISTIC analogue of `wp_while_inv` (`Laws/Loop.lean`),
and the shapes deliberately match: the body premise receives the
invariant plus a wand for "the rest of the loop", the conclusion consumes
the invariant at entry and hands the exit continuation the invariant at
the end. Two differences, both forced by the construct:

* the invariant is indexed by the REMAINING SNAPSHOT
  (`I : Array (GoValue × GoValue) → IProp`), not by a condition bit —
  the range's "how much is left" is data, not a Boolean;
* the induction is ORDINARY NAT INDUCTION on `remaining.size`, not Löb.
  The snapshot strictly shrinks at every `mapIterNext` (`eraseIdx`), so
  the loop is structurally terminating and needs no step-index; the
  `▷` that `wp_while_inv` spends its Löb hypothesis on is spent here by
  `wp_map_iter_next_key`'s own lifting.

Scope, RECORDED (v1):

* **key-only** (`for id := range c`), inherited from
  `wp_map_iter_next_key`; the key/value form lands with the law it needs.
* **normally-completing bodies only.** A body that `break`s or
  `continue`s cannot discharge `Hbody`: `Step.mapIterBreak` takes
  `.breaking (mapIterK …)` to `Config.next k` and
  `Step.mapIterContinue` takes `.continuing (mapIterK …)` back to
  `Config.next (mapIterK …)`, and the only exit `Hbody` is handed is the
  normal one (the shrunk `mapIterK`). This is a completeness scope, NOT
  a soundness side-condition — the rule is sound for any body; bodies
  with `break`/`continue` simply have no route through this premise.
  `continue` is the cheap widening (its target IS the normal one, so it
  needs only a `wp_map_iter_continue` pure-step law); `break` needs the
  rule to carry a second, break-time exit wand `∀ rem, I rem -∗ WP
  (Config.next k)`. Both are owed, neither is needed by the walks in
  flight.
* the per-iteration KEY CELL is the body's, affinely: `Hbody` receives
  `pa.id ↦ ⟨keyTy, key⟩` fresh at every iteration and is NOT asked to
  give it back, so `I` never mentions it. That is the honest model of
  the machine — `bindIterVars` allocates a NEW cell per iteration and
  nothing ever frees it — and it is what keeps `I` a function of the
  snapshot alone.

`Hbody` quantifies over EVERY array `rem`, not only over the snapshots
reachable from `entries` by erasure. That is not a strengthening of the
user's obligation in practice: `I rem` is an ANTECEDENT there, so an
invariant that carries its own reachability fact (⌜`rem` is a
sub-multiset of `entries`⌝, or an explicit disjunction over the
snapshots that can occur) discharges the unreachable instances from a
false hypothesis. The alternative — indexing the premise by a
reachability relation — buys nothing and costs a relation.

**Goose/Perennial comparison** (standing generality check). The prior art
is `wp_map_for_range` in `deps/perennial/new/golang/theory/map.v:213`
(with `wp_InternalMapForRange` at :24 and the `wp_for` family in
`theory/loop.v:71`). Read verbatim, its shape is: own the map
(`mref ↦{dq} m`), then quantify ONCE over an arbitrary key ORDER
(`∀ keys, list_to_set keys = dom m ∧ length keys = size m ∧ NoDup keys`)
and give an invariant `P keys i` indexed by that order and a POSITION in
it, with a `□`-boxed one-iteration obligation from `P keys i` to
`P keys (i+1)` and an exit from `P keys (size m)`. Four honest deltas:

1. **Where the nondeterminism is quantified.** Theirs is up-front: the
   model produces one key list and the proof then walks it in order.
   Ours is per-step — `Step.mapIterNext` picks ANY remaining index at
   EVERY step, and the body premise is discharged for an arbitrary pick
   each time. Our conclusion therefore covers interleavings a
   commit-to-a-list-first model cannot express; this is the direction the
   standing check calls fine (we may cover more).
2. **Invariant indexing.** `P keys i` (order + position) vs our
   `I remaining` (the multiset still to come). Same information given a
   fixed `entries`, but ours is what `Cont.mapIterK` already carries, so
   no ghost order needs to be introduced or maintained.
3. **Body reuse.** Their `□` is our Lean-level `∀`-quantified entailment
   premise — reusable for free, exactly as recorded for `wp_while_inv`.
4. **`break`/`continue`/`return`.** Theirs handles all three through
   `for_map_postcondition` (`map.v:207`) and the exception monad
   (`defn/exception.v`); ours v1 handles normal completion only. This is
   a real NARROWING, recorded above with its widening path — the failure
   direction the standing check names, acknowledged rather than hidden.

One further difference, not a generality claim — CORRECTED at the
2026-08-01 pre-merge audit (the first form of this note said their rule
"reads the live map"; it does not): GooseLang's `map.for_range` ALSO
iterates a snapshot — it binds `"mv" := StartRead "m"` and folds the body
over that value (`deps/perennial/new/golang/defn/map.v:40-48`, with the
verbatim source comment "Does not support modifications to the map during
the loop"), and `StartRead`'s read-lock makes a mid-loop store STUCK
(`PrepareWrite` steps only from `Reading 0`, `src/goose_lang/lang.v`).
The honest delta is therefore about mid-loop MUTATION, not about
snapshotting: Perennial EXCLUDES it (fail-closed — the program gets
stuck), while our machine PERMITS it and silently serves the stale
snapshot where Go would observe the mutation. That permissiveness is
BUG-005 (`docs/BUGS.md`), already cross-referenced in this module's
header — a semantics gap, not a proof-rule gap — and when its snapshot
surgery is scoped, Perennial offers NO live-map-iteration prior art to
copy; their model shares the snapshot design. -/
theorem wp_map_iter_inv {kid : String} {keyTy valTy : Ty} {body : Stmt}
    {entries : Array (GoValue × GoValue)} {env k}
    {I : Array (GoValue × GoValue) → IProp GF}
    (hnorm : ∀ (σ : ExecState), σ.types = GoCoreGS.types GF →
      ∀ p ∈ entries, normalizeValueForTy σ keyTy p.1 = .ok p.1)
    (Hbody : ∀ (rem : Array (GoValue × GoValue)) (i : Nat) (h : i < rem.size)
        (pa : Addr),
      iprop(I rem
        ∗ pa.id ↦ (⟨some keyTy, (rem[i]'h).1⟩ : HeapCell)
        ∗ (I (rem.eraseIdx i h) -∗
            WP (Config.next (.mapIterK (some kid) none keyTy valTy body
                  (rem.eraseIdx i h) env k)) @ s ; E {{ Φ }}))
      ⊢ WP (Config.exec body (env.pushScope.declare kid (.base pa))
              (.mapIterK (some kid) none keyTy valTy body
                (rem.eraseIdx i h) env k)) @ s ; E {{ Φ }}) :
    iprop(I entries ∗ (I #[] -∗ WP (Config.next k) @ s ; E {{ Φ }}))
      ⊢ WP (Config.next (.mapIterK (some kid) none keyTy valTy body entries env k))
          @ s ; E {{ Φ }} := by
  -- Generalize over the snapshot and induct on a size bound: every
  -- `mapIterNext` erases one entry, so the recursion is structural.
  suffices hgen : ∀ (n : Nat) (rem : Array (GoValue × GoValue)), rem.size ≤ n →
      (∀ (σ : ExecState), σ.types = GoCoreGS.types GF →
        ∀ p ∈ rem, normalizeValueForTy σ keyTy p.1 = .ok p.1) →
      iprop(I rem ∗ (I #[] -∗ WP (Config.next k) @ s ; E {{ Φ }}))
        ⊢ WP (Config.next (.mapIterK (some kid) none keyTy valTy body rem env k))
            @ s ; E {{ Φ }} from
    hgen entries.size entries (Nat.le_refl _) hnorm
  intro n
  induction n with
  | zero =>
    intro rem hsz _
    obtain rfl : rem = #[] := Array.eq_empty_of_size_eq_zero (Nat.le_zero.mp hsz)
    iintro ⟨HI, Hexit⟩
    iapply wp_map_iter_done
    iapply fupd_intro
    inext
    iapply fupd_intro
    iintro _Hcred
    iapply Hexit $$ HI
  | succ n ih =>
    intro rem hsz hn
    rcases Nat.eq_zero_or_pos rem.size with h0 | hne
    · obtain rfl : rem = #[] := Array.eq_empty_of_size_eq_zero h0
      iintro ⟨HI, Hexit⟩
      iapply wp_map_iter_done
      iapply fupd_intro
      inext
      iapply fupd_intro
      iintro _Hcred
      iapply Hexit $$ HI
    · iintro ⟨HI, Hexit⟩
      iapply (wp_map_iter_next_key (hne := hne)
        (hnorm := fun σ hσ i h => hn σ hσ _ (Array.getElem_mem h)))
      iintro %i %h %pa Hpt
      iapply (Hbody rem i h pa)
      isplitl [HI]
      · iexact HI
      isplitl [Hpt]
      · iexact Hpt
      iintro HI'
      iapply (ih (rem.eraseIdx i h)
        (by rw [Array.size_eraseIdx]; omega)
        (fun σ hσ p hp => hn σ hσ p (Array.mem_of_mem_eraseIdx hp)))
      isplitl [HI']
      · iexact HI'
      · iexact Hexit

/-! ### Witness 1 for `wp_map_iter_inv` — a NON-QUORUM program

Arc requirement (`docs/2026-08-01_proof-automation-arc.md` phase 1, and
the standing over-specialization check): the inductive range rule's FIRST
witness is not a quorum program. It is the key-only sum-over-map fold

```go
for k := range m { sum = sum + k }
```

— corpus case `range/range-map-key-sum` (differential PASS, added in this
same commit as the guardrail). The witness runs the rule over an
ARBITRARY snapshot `entries` of nonnegative `int` keys, with the
invariant "`sum` holds the total of the entries already consumed"; the
conclusion is order-independent, which is exactly what a k-entry range
walked by `wp_map_iter_next_key` alone could not have delivered without
k! branches.

Honest scope of the witness: the body statement below is a HAND-BUILT
GoCore term, not a projection of the frontend's lowering of that corpus
case. It is a witness — evidence that the rule's premises are
simultaneously satisfiable by a real program shape and that the rule
composes with the ordinary assignment/eval laws — not a claim about any
lowering (the pinned-lowering claims in `Specs/` are the ones that carry
that weight). -/

/-- The witness body: `sum = sum + k`, the loop body of
`range/range-map-key-sum`. -/
def keySumBody : Stmt := .assign (.var "sum") (.add (.var "sum") (.var "k"))

/-- The int payload of a key value (0 at a non-int value — the witness's
hypotheses rule that case out). -/
def keyInt : GoValue → Int
  | .int n _ => n
  | _ => 0

/-- The fold the witness's invariant tracks: the sum of a snapshot's key
payloads. Order-independent by construction, which is what makes it a
legitimate invariant for a nondeterministic range. -/
def keyIntSum (a : Array (GoValue × GoValue)) : Int :=
  (a.toList.map (fun p => keyInt p.1)).sum

private theorem list_map_sum_eraseIdx {α : Type _} (f : α → Int) :
    ∀ (l : List α) (i : Nat) (h : i < l.length),
      ((l.eraseIdx i).map f).sum = (l.map f).sum - f (l[i]'h)
  | _ :: t, 0, _ => by simp; omega
  | a :: t, i + 1, h => by
    have ih := list_map_sum_eraseIdx f t i (by simpa using h)
    simp only [List.eraseIdx_cons_succ, List.map_cons, List.sum_cons, ih,
      List.getElem_cons_succ]
    omega
  | [], _, h => absurd h (by simp)

private theorem list_map_sum_nonneg {α : Type _} (f : α → Int) :
    ∀ (l : List α), (∀ x ∈ l, 0 ≤ f x) → 0 ≤ (l.map f).sum
  | [], _ => by simp
  | a :: t, h => by
    have ht := list_map_sum_nonneg f t (fun x hx => h x (by simp [hx]))
    have ha := h a (by simp)
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Erasing one entry drops exactly its key from the fold. -/
theorem keyIntSum_eraseIdx {a : Array (GoValue × GoValue)} {i : Nat}
    (h : i < a.size) :
    keyIntSum (a.eraseIdx i h) = keyIntSum a - keyInt (a[i]'h).1 := by
  unfold keyIntSum
  rw [Array.toList_eraseIdx]
  exact list_map_sum_eraseIdx _ a.toList i (by simpa using h)

/-- A snapshot of nonnegative keys has a nonnegative fold. -/
theorem keyIntSum_nonneg {a : Array (GoValue × GoValue)}
    (h : ∀ p ∈ a, 0 ≤ keyInt p.1) : 0 ≤ keyIntSum a :=
  list_map_sum_nonneg _ a.toList (fun x hx => h x (Array.mem_def.mpr hx))

/-- `int` is 64-bit two's complement; a nonnegative value below `2^63`
rides through `IntKind.normalize` unchanged. -/
theorem int_normalize_of_nonneg_lt {v : Int} (h0 : 0 ≤ v) (h1 : v < 2 ^ 63) :
    IntKind.int.normalize v = v := by
  have hmod : v % (2 : Int) ^ 64 = v := Int.emod_eq_of_lt h0 (by omega)
  simp only [IntKind.normalize, IntKind.bits?, IntKind.signed, hmod, if_true,
    if_neg (show ¬ (v ≥ (2 : Int) ^ (64 - 1)) by omega)]

/-- **WITNESS 1 (non-quorum): `for k := range m { sum = sum + k }`.**
Over an ARBITRARY snapshot of nonnegative `int` keys whose total fits in
an `int`, the range leaves `sum` holding that total — for every one of
the `entries.size!` iteration orders the machine may choose, discharged
through `wp_map_iter_inv` by ONE generic-iteration obligation.

The per-iteration key cell is used (the body reads `k`) and then dropped
affinely, which is the rule's stated treatment of it; the invariant
mentions only `sum` and the snapshot. -/
theorem wp_map_iter_inv_key_sum_witness {acc : Addr} {valTy : Ty} {env k}
    {entries : Array (GoValue × GoValue)}
    (hkeys : ∀ p ∈ entries, ∃ m : Int, p.1 = .int m .int ∧ 0 ≤ m ∧ m < 2 ^ 63)
    (hbound : keyIntSum entries < 2 ^ 63)
    (hacc : LocalEnv.lookup env "sum" = some (.base acc)) :
    acc.id ↦ (⟨some (.int .int), .int 0 .int⟩ : HeapCell)
      ∗ (acc.id ↦ (⟨some (.int .int), .int (keyIntSum entries) .int⟩ : HeapCell)
          -∗ WP (Config.next k) @ s ; E {{ Φ }})
      ⊢ WP (Config.next (.mapIterK (some "k") none (.int .int) valTy keySumBody
              entries env k)) @ s ; E {{ Φ }} := by
  iintro ⟨Hacc, Hexit⟩
  iapply (wp_map_iter_inv
    (I := fun rem => iprop(∃ v : Int,
      ⌜v = keyIntSum entries - keyIntSum rem
        ∧ 0 ≤ keyIntSum rem ∧ keyIntSum rem ≤ keyIntSum entries
        ∧ ∀ p ∈ rem, ∃ m : Int, p.1 = .int m .int ∧ 0 ≤ m ∧ m < 2 ^ 63⌝
        ∗ acc.id ↦ (⟨some (.int .int), .int v .int⟩ : HeapCell)))
    (hnorm := by
      intro σ _hσ p hp
      obtain ⟨m, hm, hm0, hm1⟩ := hkeys p hp
      rw [hm]
      simp [normalizeValueForTy, normalizeValueForTyFuel,
        int_normalize_of_nonneg_lt hm0 hm1])
    (Hbody := by
      intro rem i h pa
      iintro ⟨⟨%v, %hv, Hacc⟩, Hkey, Hk⟩
      obtain ⟨hv0, hnn, hle, hmem⟩ := hv
      obtain ⟨m, hm, hm0, hm1⟩ := hmem (rem[i]'h) (Array.getElem_mem h)
      -- the fold after this iteration, and the two bounds the store needs
      have herase : keyIntSum (rem.eraseIdx i h) = keyIntSum rem - m := by
        rw [keyIntSum_eraseIdx h, hm]; rfl
      have hmem' : ∀ p ∈ rem.eraseIdx i h,
          ∃ m : Int, p.1 = .int m .int ∧ 0 ≤ m ∧ m < 2 ^ 63 :=
        fun p hp => hmem p (Array.mem_of_mem_eraseIdx hp)
      have hnn' : 0 ≤ keyIntSum (rem.eraseIdx i h) :=
        keyIntSum_nonneg (fun p hp => by
          obtain ⟨m', hm', hm0', -⟩ := hmem' p hp
          rw [hm']; exact hm0')
      have hsum : v + m = keyIntSum entries - keyIntSum (rem.eraseIdx i h) := by
        omega
      have hlo : 0 ≤ v + m := by omega
      have hhi : v + m < 2 ^ 63 := by omega
      rw [hm]
      -- `sum = sum + k`
      unfold keySumBody
      iapply (wp_assign_start (te := .ref "sum") rfl)
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
      iapply wp_assign_target
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
      iapply Hk
      iexists (v + m)
      isplitl []
      · ipureintro
        exact ⟨hsum, hnn', by omega, hmem'⟩
      · iexact Hacc))
  isplitl [Hacc]
  · iexists (0 : Int)
    isplitl []
    · ipureintro
      exact ⟨by omega, keyIntSum_nonneg (fun p hp => by
        obtain ⟨m, hm, hm0, -⟩ := hkeys p hp
        rw [hm]; exact hm0), Int.le_refl _, hkeys⟩
    · iexact Hacc
  · iintro ⟨%v, %hv, Hacc⟩
    obtain ⟨hv0, -, -, -⟩ := hv
    have : v = keyIntSum entries := by
      simpa [keyIntSum] using hv0
    subst this
    iapply Hexit $$ Hacc

end

end GoLean.Iris
