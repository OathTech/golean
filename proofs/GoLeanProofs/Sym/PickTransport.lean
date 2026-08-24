import GoLeanProofs.Sym.TableExt

/-!
# The map-range pick transport (A4-U9: the U4 promotion-ledger lift,
coordinator-authorized additive touch)

**LINEAGE: symbolic-execution path-condition splitting at a
nondeterministic-choice site (the choice-consumption boundary of the
refinement template — design `2026-08-22_campaign-arc4-sym-extension-
design.md` §4(ii)), realized as the composition of the kit's
`stepFn_pick_generic` (the type-generic pick step) with `alloc_conc`
(the mirror-side symbolic-cell allocation).**

Lifted VERBATIM from `Specs/Raft/BfSteps.lean` (which retains its own
copy as shipped history — zero edits to shipped modules; consumers at
lift time: BfSteps, BcSteps, Bc31, Bf31, and every future handler's
range loop — the ≥2-consumer promotion rule met four times over).
The statement is raft-independent: only Sym/machine vocabulary. A
pick fact at a site needs (a) one heavy γ-heap fact (the live-entry
walk), (b) cheap literal-level candidate/consume/index facts, and
(c) a normalize-identity side lemma for the picked key; the picked
key enters as a symbolic-cell alloc, so ONE post-window serves every
pick (the §4(ii) collapse). `vo = none`: key-only range binders (both
census range sites; a key+value binder variant is future work on its
first consumer).
-/

namespace GoLean.Sym

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Surface

/-- THE PICK TRANSPORT: a map-range pick at a γ-image, with the key
entering as a symbolic-cell alloc on the mirror side. -/
theorem stepFn_pick_transport (ρ : Valuation) (σ : ExecState)
    {S : SymState} {name : String} {kt vt : Ty} {body : Stmt}
    {base : Option Loc} {produced start : Array SymValue}
    {env : LocalEnv} {k : GoLean.Sym.Cont symDom}
    {keyv : SymValue} {cands : Array (GoValue × GoValue)} {mand : Bool}
    {idx : Nat} {ch ch' : Choices} {kv vv : GoValue}
    (hcands : mapIterCandidates (γS ρ σ S) kt vt base
      (produced.map (concV (symInterp ρ))) = .ok cands)
    (hne : cands.isEmpty = false)
    (hmand : mapIterMandatoryRemains (γS ρ σ S) kt cands
      (start.map (concV (symInterp ρ))) = .ok mand)
    (hconsume : Choices.consume ch (cands.size + (if mand then 0 else 1))
      = (idx, ch'))
    (hget : cands[idx]? = some (kv, vv))
    (hkey : concV (symInterp ρ) keyv = kv)
    (hnorm : normalizeValueForTy (γS ρ σ S) kt kv = .ok kv) :
    stepFn (γS ρ σ S)
      (γC ρ (.next (.mapIterK (some name) none kt vt body base produced
        start env k))) ch
      = .ok (γC ρ (.exec body
            ((env.pushScope).declare name (S.alloc keyv (some kt)).1)
            (.mapIterK (some name) none kt vt body base
              (produced.push keyv) start env k)),
          γS ρ σ (S.alloc keyv (some kt)).2, ch') := by
  have halloc := alloc_conc (I := symInterp ρ) σ S keyv (some kt)
  have hbind : bindIterVars env.pushScope (γS ρ σ S) (some name) none kt vt
      kv vv
      = .ok ((env.pushScope).declare name (S.alloc keyv (some kt)).1,
          γS ρ σ (S.alloc keyv (some kt)).2) := by
    simp only [bindIterVars, hnorm, Bind.bind, Except.bind, pure,
      Except.pure]
    rw [← hkey, halloc]
  have hstep := stepFn_pick_generic (body := body)
    (k := concK (symInterp ρ) k) hcands hne hmand hconsume hget hbind
  refine Eq.trans hstep ?_
  simp only [concC, concK, Array.map_push, hkey]

end GoLean.Sym
