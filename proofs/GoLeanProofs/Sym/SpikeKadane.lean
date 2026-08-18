import GoLeanProofs.Sym.Drift
import GoLeanProofs.Examples.Kadane

/-!
# THE KERNEL-COST SPIKE (WP arc slice 4, phase 1, deliverable 4)

The design's mandatory gate (`docs/2026-08-16_symbolic-domain-design.md`
§6.2), BEFORE the commutation walk: transport ONE real shipped window —
Kadane's setup loop head, `kd_su_A0_raw`
(`Examples/Kadane.lean:1258`) — through the evaluator, via a
HAND-INSTANTIATED refinement-shaped lemma for JUST that window's
fragment (a bespoke mini-soundness, NOT the general theorem), and
measure the per-window cost against the `with_unfolding_all rfl`
baseline. Numbers recorded derivation-anchored in
`docs/wp-arc-log/s4.md`.

The bespoke pieces:
- `spikeFrag` — a syntactic whitelist of exactly the configuration
  shapes the A0 window steps through (the trace: exec
  while/if/seqn/block/assign; evalE var/ref/boolLit/lessCmp; retV at
  whileK/ifK-on-closed-bool, tgtOpK, rhsK-vals, strictK-lessCmp; next
  at seq/storeK-with-base-chain-refs);
- `spikeStep_sound` — the refinement-SHAPED per-step transport
  (`stepFnS S C = .ok → spikeFrag C → ∀ ρ σ ch, stepFn (γS ρ σ S)
  (γC ρ C) ch = .ok (γ-image)`), proven only over the whitelist
  (everything else is refuted by the guard — which is what makes this
  bespoke rather than the general walk);
- `spikeWindow` — the guard-checked driver, and its soundness by
  induction;
- `kd_su_A0_via_sym` — the shipped window's statement, BYTE-IDENTICAL
  to `kd_su_A0_raw`, discharged by one `rfl` evaluator run + one
  soundness application + the γ-image conversion. Its hand twin stays
  in-tree as the direct diff (design §6.3).

This file is Kadane-specific ON PURPOSE (a witness instantiation, not
kit surface); the general walk is `Sym/Drift.lean`'s phase-2 arc.
-/

namespace GoLean.Sym.Spike

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym
open GoLean.Examples.Kadane

/-! ## The window's fragment guard -/

/-- Is a target ref an empty chain at a concrete address (the only
store shape the A0 window performs)? -/
def baseRef : TargetRef symDom → Bool
  | .chain anchor idxs steps =>
      (match anchor with | .addr _ => true | _ => false)
        && idxs.isEmpty && steps.isEmpty
  | .mapElem _ _ _ _ => false

/-- Statement shapes of the window (one-level match so guard
refutations reduce mechanically). -/
def fragStmt : Stmt → Bool
  | .while _ _ => true
  | .ifThenElse _ _ _ => true
  | .seqn _ => true
  | .block decls _ => decls.isEmpty
  | .assign _ _ => true
  | _ => false

/-- Expression shapes of the window. -/
def fragExpr : Expr → Bool
  | .boolLit _ => true
  | .var _ => true
  | .ref _ => true
  | .lessCmp _ _ => true
  | _ => false

/-- Value-delivery shapes of the window: branches only on CLOSED bools;
target/store spines; the `lessCmp` strict frame. -/
def fragRet : SymValue → SymCont → Bool
  | .bool b, .whileK _ _ _ _ => (symDom.toBool? b).isSome
  | .bool b, .ifK _ _ _ _ => (symDom.toBool? b).isSome
  | _, .tgtOpK _ _ _ _ _ _ _ _ _ _ _ => true
  | _, .rhsK .vals _ _ _ _ _ _ => true
  | _, .strictK .lessCmp _ _ _ _ => true
  | _, _ => false

/-- Completion shapes of the window. -/
def fragNext : SymCont → Bool
  | .seq _ _ _ => true
  | .storeK refs _ _ _ _ => refs.all baseRef
  | _ => false

/-- The A0 window's configuration-shape whitelist. A `false` here makes
the guarded driver answer `none` — the window visibly leaves the spike
fragment, never a wrong transport. -/
def spikeFrag : SymConfig → Bool
  | .exec stmt _ _ => fragStmt stmt
  | .evalE e _ _ => fragExpr e
  | .retV v k => fragRet v k
  | .next k => fragNext k
  | _ => false

/-! ## Small window-local commutation pieces -/

variable {ρ : Valuation}

theorem completeRef_conc (sh : TargetShape) (vs : List SymValue) :
    completeTargetRef sh (vs.map (γV ρ))
      = (completeTargetRef' sh vs).map (concRef (symInterp ρ)) := by
  cases sh with
  | chain steps =>
      cases vs with
      | nil => rfl
      | cons a rest =>
          simp only [List.map_cons, completeTargetRef, completeTargetRef',
            List.length_map]
          by_cases hlen : rest.length = indexStepCount steps
          · rw [if_pos hlen, if_pos hlen]
            rfl
          · rw [if_neg hlen, if_neg hlen]
            rfl
  | mapElem kt vt =>
      rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
        simp [completeTargetRef, completeTargetRef', concRef]

/-- The strict-op apply at `lessCmp`, transported (the one op the A0
window applies). -/
theorem applyLess_conc (σ : ExecState) {s : SymState} {vs : List SymValue}
    {out : SymValue} {s' : SymState}
    (h : applyStrictOp' s .lessCmp vs = .ok (out, s')) :
    applyStrictOp (γS ρ σ s) .lessCmp (vs.map (γV ρ))
      = .ok (γV ρ out, γS ρ σ s') := by
  rcases vs with _ | ⟨l, _ | ⟨r, _ | ⟨x, rest⟩⟩⟩ <;>
    simp only [applyStrictOp', quit] at h <;> try (cases h; done)
  simp only [bind_eq_ok] at h
  obtain ⟨b, hb, hout⟩ := h
  cases hout
  simp only [List.map_cons, List.map_nil, applyStrictOp, bind_eq_ok]
  exact ⟨_, valueLess_conc (symInterp_sound ρ) hb, by simp⟩

/-- The A0 store shape: an empty chain at a concrete address. -/
theorem storeBaseRef_conc (σ : ExecState) {s : SymState}
    {r : TargetRef symDom} (hr : baseRef r = true) {v : SymValue}
    {s' : SymState} (h : storeTarget' s r v = .ok s') :
    storeTarget (γS ρ σ s) (concRef (symInterp ρ) r) (γV ρ v)
      = .ok (γS ρ σ s') := by
  cases r with
  | mapElem b k kt vt => simp [baseRef] at hr
  | chain anchor idxs steps =>
      cases idxs with
      | cons i rest =>
          cases steps with
          | nil =>
              exfalso
              simp [storeTarget', resolveChain', quit, Bind.bind,
                Except.bind] at h
          | cons st srest => simp [baseRef] at hr
      | nil =>
          cases steps with
          | cons st srest => simp [baseRef] at hr
          | nil =>
              cases anchor <;>
                (try (exfalso
                      simp [storeTarget', resolveChain', Value.asLoc, quit,
                        Bind.bind, Except.bind] at h
                      done))
              next loc =>
                simp only [storeTarget', resolveChain', Value.asLoc,
                  Bind.bind, Except.bind] at h
                simp only [storeTarget, concRef, List.map_nil,
                  resolveChain, concV_addr, valueAsLoc, Bind.bind,
                  Except.bind]
                exact storeLoc_conc (symInterp_sound ρ) σ h

/-! ## The bespoke per-step transport -/

/-- The refinement-SHAPED per-step transport for the A0 window's
fragment: a successful, guard-approved mirror step transports to the
machine, for EVERY valuation, table-carrier, and choice stream (the
`∀ρ ∀σ ∀ch, ch`-unchanged claims, on this fragment). Everything
outside the whitelist is refuted by the guard — this is deliberately
NOT the general walk (design §6.2's spike instruction). -/
theorem spikeStep_sound {S : SymState} {C : SymConfig}
    {C₁ : SymConfig} {S₁ : SymState}
    (h : stepFnS S C = .ok (C₁, S₁)) (hg : spikeFrag C = true)
    (ρ : Valuation) (σ : ExecState) (ch : Choices) :
    stepFn (γS ρ σ S) (γC ρ C) ch = .ok (γC ρ C₁, γS ρ σ S₁, ch) := by
  cases C with
  | exec stmt env k =>
      simp only [spikeFrag] at hg
      cases stmt <;> simp only [fragStmt] at hg <;>
        try (exact Bool.noConfusion hg)
      case seqn ss =>
        cases h
        simp only [γC, concC, stepFn, seqCont_conc]
        rfl
      case block decls ss =>
        have hd : decls = #[] := Array.isEmpty_iff.mp hg
        subst hd
        cases h
        rfl
      case assign lhs rhs =>
        rcases hplan : targetPlan lhs with _ | ⟨sh, _ | ⟨e, ops⟩⟩ <;>
          (simp only [stepFnS, stepFn'] at h; rw [hplan] at h)
        · cases h
        · cases h
        · cases h
          simp only [γC, concC, concK, stepFn]
          rw [hplan]
          rfl
      case ifThenElse c t e =>
        cases h
        rfl
      case «while» c b =>
        cases h
        rfl
  | evalE e env k =>
      simp only [spikeFrag] at hg
      cases e <;> simp only [fragExpr] at hg <;>
        try (exact Bool.noConfusion hg)
      case var id =>
        rcases hlk : LocalEnv.lookup env id with _ | loc <;>
          (simp only [stepFnS, stepFn'] at h; rw [hlk] at h)
        · cases h
        · simp only [bind_eq_ok] at h
          obtain ⟨v, hv, hout⟩ := h
          cases hout
          simp only [γC, concC, stepFn]
          rw [hlk]
          simp only [bind_eq_ok]
          exact ⟨_, loadLoc_conc σ hv, rfl⟩
      case boolLit b =>
        cases h
        simp [stepFn, concC, γB, symInterp, pure, Except.pure]
      case ref id =>
        rcases hlk : LocalEnv.lookup env id with _ | loc <;>
          (simp only [stepFnS, stepFn'] at h; rw [hlk] at h)
        · cases h
        · cases h
          simp only [γC, concC, stepFn]
          rw [hlk]
          simp [pure, Except.pure]
      case lessCmp l r =>
        cases h
        rfl
  | retV v k =>
      simp only [spikeFrag] at hg
      cases k <;> try (simp only [fragRet] at hg; exact Bool.noConfusion hg)
      case whileK c b env k' =>
        cases v <;> simp only [fragRet] at hg <;>
          try (exact Bool.noConfusion hg)
        next bR =>
          rcases hb : closedB? bR with _ | bb
          · exact absurd hg (by simp [hb])
          · simp only [stepFnS, stepFn', Value.asBoolAt] at h
            first
              | rw [hb] at h
              | rw [show symDom.toBool? bR = some bb from hb] at h
            simp only [Bind.bind, Except.bind] at h
            have hγ : γB ρ bR = bb := closedB?_sound ρ hb
            cases bb <;> cases h <;>
              simp [γC, concC, concK, symInterp, stepFn, valueAsBool, hγ,
                Bind.bind, Except.bind, pure, Except.pure]
      case ifK t e env k' =>
        cases v <;> simp only [fragRet] at hg <;>
          try (exact Bool.noConfusion hg)
        next bR =>
          rcases hb : closedB? bR with _ | bb
          · exact absurd hg (by simp [hb])
          · simp only [stepFnS, stepFn', Value.asBoolAt] at h
            first
              | rw [hb] at h
              | rw [show symDom.toBool? bR = some bb from hb] at h
            simp only [Bind.bind, Except.bind] at h
            have hγ : γB ρ bR = bb := closedB?_sound ρ hb
            cases bb <;> cases h <;>
              simp [γC, concC, concK, symInterp, stepFn, valueAsBool, hγ,
                Bind.bind, Except.bind, pure, Except.pure]
      case strictK op done pending env k' =>
        cases op <;> simp only [fragRet] at hg <;>
          try (exact Bool.noConfusion hg)
        cases pending with
        | cons e rest =>
            cases h
            rfl
        | nil =>
            simp only [stepFnS, stepFn', bind_eq_ok] at h
            obtain ⟨⟨out, s'⟩, happ, hout⟩ := h
            cases hout
            simp only [γC, concC, concK, stepFn]
            have := applyLess_conc (ρ := ρ) σ happ
            simp only [List.map_reverse, List.map_cons] at this ⊢
            rw [this]
            rfl
      case tgtOpK sh ops pending refs targets rop rhs vals body env k' =>
        cases pending with
        | cons e rest =>
            cases h
            rfl
        | nil =>
            simp only [stepFnS, stepFn'] at h
            rcases hcomp : completeTargetRef' sh (v :: ops).reverse
                with _ | r
            · rw [hcomp] at h
              cases h
            · rw [hcomp] at h
              have hcompm := completeRef_conc (ρ := ρ) sh (v :: ops).reverse
              rw [hcomp] at hcompm
              simp only [List.map_reverse, List.map_cons] at hcompm
              cases targets with
              | cons tp rest =>
                  obtain ⟨sh', ops'⟩ := tp
                  cases ops' with
                  | nil => cases h
                  | cons e' rest' =>
                      cases h
                      simp only [γC, concC, concK, stepFn]
                      rw [hcompm]
                      simp [Option.map]
              | nil =>
                  cases rhs with
                  | cons e' rest' =>
                      cases h
                      simp only [γC, concC, concK, stepFn]
                      rw [hcompm]
                      simp [Option.map]
                  | nil =>
                      cases h
                      simp only [γC, concC, concK, stepFn]
                      rw [hcompm]
                      simp [Option.map]
      case rhsK rop refs done pending body env k' =>
        cases rop <;> simp only [fragRet] at hg <;>
          try (exact Bool.noConfusion hg)
        cases pending with
        | cons e rest =>
            cases h
            rfl
        | nil =>
            simp only [stepFnS, stepFn', applyRhsOp', Bind.bind,
              Except.bind] at h
            cases h
            simp only [γC, concC, concK, stepFn, applyRhsOp,
              pure, Except.pure]
            simp [List.map_reverse]
  | next k =>
      simp only [spikeFrag] at hg
      cases k <;> try (simp only [fragNext] at hg; exact Bool.noConfusion hg)
      case seq rest env k' =>
        cases rest with
        | nil =>
            cases h
            rfl
        | cons t ts =>
            cases h
            rfl
      case storeK refs vals body env k' =>
        cases refs with
        | nil =>
            cases vals with
            | nil =>
                cases h
                rfl
            | cons val vrest =>
                cases h
        | cons r rs =>
            have hr : baseRef r = true ∧ rs.all baseRef = true := by
              simp only [fragNext, List.all_cons, Bool.and_eq_true] at hg
              exact hg
            cases vals with
            | nil => cases h
            | cons val vrest =>
                simp only [stepFnS, stepFn', bind_eq_ok] at h
                obtain ⟨s', hstore, hout⟩ := h
                cases hout
                simp only [γC, concC, stepFn, concK, List.map_cons]
                rw [storeBaseRef_conc σ hr.1 hstore]
                rfl
  | breaking k => simp only [spikeFrag] at hg; exact Bool.noConfusion hg
  | continuing k => simp only [spikeFrag] at hg; exact Bool.noConfusion hg
  | returning k => simp only [spikeFrag] at hg; exact Bool.noConfusion hg
  | breakingTo L k => simp only [spikeFrag] at hg; exact Bool.noConfusion hg
  | continuingTo L k => simp only [spikeFrag] at hg; exact Bool.noConfusion hg
  | panicking chain k => simp only [spikeFrag] at hg; exact Bool.noConfusion hg
  | panicked msg => simp only [spikeFrag] at hg; exact Bool.noConfusion hg
  | blockedSend a b c => simp only [spikeFrag] at hg; exact Bool.noConfusion hg
  | blockedRecv a b c d e => simp only [spikeFrag] at hg; exact Bool.noConfusion hg
  | blockedSelect a b c => simp only [spikeFrag] at hg; exact Bool.noConfusion hg
  | spawned k => simp only [spikeFrag] at hg; exact Bool.noConfusion hg
  | blockedSync a b c d => simp only [spikeFrag] at hg; exact Bool.noConfusion hg

/-! ## The guarded window driver -/

/-- Guard-checked evaluation: `none` = the run left the spike fragment
(visible refusal, never a wrong transport); a quit ENDS the window
(shorter `n`), per the ruled OQ2 driver discipline. -/
def spikeWindow : Nat → SymState → SymConfig →
    Option (Nat × SymState × SymConfig)
  | 0, S, C => some (0, S, C)
  | budget + 1, S, C =>
      match stepFnS S C with
      | .error _ => some (0, S, C)
      | .ok (C', S') =>
          if spikeFrag C then
            match spikeWindow budget S' C' with
            | some (n, S'', C'') => some (n + 1, S'', C'')
            | none => none
          else none

/-- The bespoke WINDOW transport: a guard-approved run of `n` steps
transports to an `n`-step `stepFnIter` fact, ∀ρ ∀σ ∀ch with `ch`
unchanged — the refinement theorem's exact shape (design §6.1), on
the spike fragment. -/
theorem spikeWindow_sound :
    ∀ {budget : Nat} {S : SymState} {C : SymConfig} {n : Nat}
      {S' : SymState} {C' : SymConfig},
      spikeWindow budget S C = some (n, S', C') →
      ∀ (ρ : Valuation) (σ : ExecState) (ch : Choices),
        stepFnIter n (γS ρ σ S) (γC ρ C) ch
          = .ok (γC ρ C', γS ρ σ S', ch) := by
  intro budget
  induction budget with
  | zero =>
      intro S C n S' C' h ρ σ ch
      simp only [spikeWindow] at h
      cases h
      rfl
  | succ budget ih =>
      intro S C n S' C' h ρ σ ch
      simp only [spikeWindow] at h
      rcases hstep : stepFnS S C with q | ⟨C₁, S₁⟩
      · rw [hstep] at h
        cases h
        rfl
      · rw [hstep] at h
        dsimp only at h
        by_cases hg : spikeFrag C = true
        · rw [if_pos hg] at h
          rcases hrec : spikeWindow budget S₁ C₁ with _ | ⟨m, S₂, C₂⟩
          · rw [hrec] at h
            cases h
          · rw [hrec] at h
            cases h
            have h1 := spikeStep_sound hstep hg ρ σ ch
            have h2 := ih hrec ρ σ ch
            simp only [stepFnIter, h1, Bind.bind, Except.bind]
            exact h2
        · rw [if_neg hg] at h
          cases h

/-! ## The Kadane A0 window fixtures (design §5.2's instantiation,
hand-written reflect-free so the kernel reduces them; validated by
`#guard` BEFORE any rfl — the #eval-before-decide rule) -/

/-- A symbolic-int64 cell at symbol `i`. -/
def suCell (i : Nat) : HeapCell symDom :=
  .mk (some (.int .int64)) (.int (.var i) .int64)

/-- The setup-loop heap front (`kHeapSu nv sv n l iv flag`'s symbolic
form): vars 0/1/2 = nv/sv/iv; CELL atoms 0/1/2 = the symbolic-length
handle/backing/handle cells 4–6 (JC-6). -/
def suHeap (flag : SymBool) : SymHeap :=
  [(.base ⟨0⟩, suCell 0), (.base ⟨1⟩, suCell 1),
   (.base ⟨2⟩, .mk (some (.array 8 (.int .int64)))
      (.array ⟨List.replicate 8 (.int (.lit 0) .int64)⟩)),
   (.base ⟨3⟩, .mk (some (.int .int64)) (.int (.lit 0) .int64)),
   (.base ⟨4⟩, .atom 0), (.base ⟨5⟩, .atom 1), (.base ⟨6⟩, .atom 2),
   (.base ⟨7⟩, suCell 2),
   (.base ⟨8⟩, .mk (some .bool) (.bool flag))]

def suS0 : SymState := { heap := suHeap (.lit true), nextAddr := 9 }
def suS25 : SymState := { heap := suHeap (.lit false), nextAddr := 9 }
def suFrameStop : SymCont := .frame [] [] [] [] .stop false
def suTailAfterSetup : SymCont :=
  .seq [kdS4, kdS5, kdS6, kdS7] [kSScope, kBaseScope] suFrameStop
def suHeadTail : SymCont :=
  .seq [] kSuEnv
    (.seq [] [[("i", .base ⟨7⟩)], kSScope, kBaseScope] suTailAfterSetup)
def suC0 : SymConfig :=
  .exec (.while (.boolLit true) kdSuWhileBody) kSuEnv suHeadTail
def suLoopK : SymCont := .loop (.boolLit true) kdSuWhileBody kSuEnv suHeadTail
def suCmpK : SymCont :=
  .ifK (.seqn #[]) .breakStmt kSuEnv1 (.seq [kdSuStoreBlock] kSuEnv1 suLoopK)
def suC25 : SymConfig := .retV (.bool (.ltI (.var 2) (.var 0))) suCmpK

/-- The §5.2 valuation: the hand lemma's binders as the symbols'
values. -/
def kdρ (nv sv iv : Int) (n : Nat) (l : List Int) : Valuation where
  ints := fun i => if i = 0 then nv else if i = 1 then sv else iv
  bools := fun _ => false
  vals := fun _ => .nil
  cells := fun i =>
    if i = 0 then kHandle n else if i = 1 then kBack n l else kHandle n

-- Compiled-evaluation guards BEFORE the kernel rfl (the
-- #eval-before-decide rule): the run completes 25 guard-approved steps.
#guard (spikeWindow 25 suS0 suC0).map (fun r => r.1) == some 25

/-! ## γ-image conversions (the transported statement lands on the hand
lemma's exact spellings) -/

theorem γ_suS (σ : ExecState) (nv sv iv : Int) (n : Nat) (l : List Int)
    (b : Bool) :
    γS (kdρ nv sv iv n l) σ { heap := suHeap (.lit b), nextAddr := 9 }
      = kSt σ (kHeapSu nv sv n l iv b) 9 := by
  simp [γS, concS, concHeap, suHeap, suCell, concCell, kdρ, symInterp,
    γB, γI, kHeapSu, kHeap0, ki64, kbool, kHandle, kBack, kArr8,
    kZeros8, List.replicate]

theorem γ_suC0 (nv sv iv : Int) (n : Nat) (l : List Int) :
    γC (kdρ nv sv iv n l) suC0 = kdSuHeadCfg := by
  simp [γC, concC, concK, suC0, suHeadTail, suTailAfterSetup,
    suFrameStop, kdSuHeadCfg, kdSuHeadTail, kdTailAfterSetup,
    kdFrameStop]

theorem γ_suC25 (nv sv iv : Int) (n : Nat) (l : List Int) :
    γC (kdρ nv sv iv n l) suC25
      = .retV (.bool (decide (iv < nv))) kdSuCmpK := by
  simp [γC, concC, concK, suC25, suCmpK, suLoopK, suHeadTail,
    suTailAfterSetup, suFrameStop, kdSuCmpK, kdSuLoopK, kdSuHeadTail,
    kdTailAfterSetup, kdFrameStop, symInterp, γB, γI, kdρ]

/-! ## THE TRANSPORTED WINDOW (the measured deliverable) -/

set_option profiler true in
set_option profiler.threshold 1 in
/-- `kd_su_A0_raw`'s statement, BYTE-IDENTICAL
(`Examples/Kadane.lean:1258`), discharged through the evaluator: one
`rfl` evaluator run + one soundness application + the γ conversions.
The hand twin stays in-tree as the direct diff; the measured numbers
live in `docs/wp-arc-log/s4.md` (the spike gate record). -/
theorem kd_su_A0_via_sym (σ : ExecState) (nv sv : Int) (n : Nat)
    (l : List Int) (iv : Int) (ch : Choices) :
    stepFnIter 25 (kSt σ (kHeapSu nv sv n l iv true) 9) kdSuHeadCfg ch
      = .ok (.retV (.bool (decide (iv < nv))) kdSuCmpK,
          kSt σ (kHeapSu nv sv n l iv false) 9, ch) := by
  have hrun : spikeWindow 25 suS0 suC0 = some (25, suS25, suC25) := by rfl
  have ht := spikeWindow_sound hrun (kdρ nv sv iv n l) σ ch
  simp only [show suS0 = { heap := suHeap (.lit true), nextAddr := 9 } from rfl,
    show suS25 = { heap := suHeap (.lit false), nextAddr := 9 } from rfl] at ht
  rw [γ_suC0, γ_suC25, γ_suS (b := true), γ_suS (b := false)] at ht
  exact ht

end GoLean.Sym.Spike
