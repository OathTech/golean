import GoLean.GoCore.BooleanControlTyping
import GoLean.GoCore.Machine

/-! Structural Boolean machine control. The parameters `root` and `roots`
describe actual root cells and all saved environment bindings; the final
runtime invariant instantiates them with Boolean store predicates. They do
not assert successful execution or closure under future steps. -/
namespace GoLean.GoCore.BooleanRuntime
open BooleanTyping Admission Machine

def Covers (Γ : Context) (env : LocalEnv) : Prop :=
  ∀ name, Bound Γ name → ∃ loc, env.lookup name = some loc

theorem Covers.empty (env : LocalEnv) : Covers [] env := by
  intro name hn
  simp [Bound] at hn

theorem Covers.mono {Γ Δ env} (h : Covers Δ env) (inc : Included Γ Δ) : Covers Γ env :=
  fun name hn => h name (inc name hn)

theorem Covers.append {Γ Δ env} (h : Covers Γ env) (h' : Covers Δ env) :
    Covers (Γ ++ Δ) env := by
  rintro name ⟨scope, hs, hn⟩
  rcases List.mem_append.mp hs with hs | hs
  · exact h name ⟨scope, hs, hn⟩
  · exact h' name ⟨scope, hs, hn⟩

/-- A statement continuation always has an entry barrier to catch returns.
The terminal `.stop` is admitted only as `.next .stop`, never as a return
destination or continuation for another statement. -/
inductive ReturnCont (roots : LocalEnv → Prop) : Cont → Prop
  | barrier : ReturnCont roots (.frame [] [] [] [] .stop)
  | seq {Γ env ss k} : Covers Γ env → roots env → ControlStmts Γ ss →
      ReturnCont roots k → ReturnCont roots (.seq ss env k)

inductive BoolCont (root : Loc → Prop) (roots : LocalEnv → Prop) : Cont → Prop
  | not {env k} : roots env → BoolCont root roots k →
      BoolCont root roots (.strictK .not [] [] env k)
  | and {Γ e env k} : Covers Γ env → roots env → ExprTyped Γ e →
      BoolCont root roots k → BoolCont root roots (.andK e env k)
  | or {Γ e env k} : Covers Γ env → roots env → ExprTyped Γ e →
      BoolCont root roots k → BoolCont root roots (.orK e env k)
  | coerce {k} : BoolCont root roots k → BoolCont root roots (.boolK k)
  | branch {Γ t f env k} : Covers Γ env → roots env →
      ControlStmt false Γ t → ControlStmt false Γ f → ReturnCont roots k →
      BoolCont root roots (.ifK t f env k)
  | rhs {loc env k} : root loc → roots env → ReturnCont roots k →
      BoolCont root roots (.rhsK .vals [.chain (.addr loc) [] []] [] [] (.seqn #[]) env k)

/-- Only assignment-generated `.ref` evaluation has address sort. -/
inductive AddrCont (roots : LocalEnv → Prop) : Cont → Prop
  | target {Γ e env k} : Covers Γ env → roots env → ExprTyped Γ e → ReturnCont roots k →
      AddrCont roots (.tgtOpK (.chain []) [] [] [] [] .vals [e] [] (.seqn #[]) env k)

inductive Control (root : Loc → Prop) (roots : LocalEnv → Prop) : Config → Prop
  | terminal : Control root roots (.next .stop)
  | next {k} : ReturnCont roots k → Control root roots (.next k)
  | exec {Γ stmt env k} : Covers Γ env → roots env → ControlStmt false Γ stmt →
      ReturnCont roots k → Control root roots (.exec stmt env k)
  /-- The tail may use names that this head has not allocated yet. This
  joint constructor supplies exactly that declaration-effect boundary. -/
  | execSeq {Γ stmt rest env k} : Covers Γ env → roots env →
      ControlStmt true Γ stmt → ControlStmts (afterStmt Γ stmt) rest →
      ReturnCont roots k → Control root roots (.exec stmt env (.seq rest env k))
  | evalBool {Γ e env k} : Covers Γ env → roots env → ExprTyped Γ e →
      BoolCont root roots k → Control root roots (.evalE e env k)
  | evalRef {Γ name env k} : Covers Γ env → roots env → Bound Γ name →
      AddrCont roots k → Control root roots (.evalE (.ref name) env k)
  | retBool {b k} : BoolCont root roots k → Control root roots (.retV (.bool b) k)
  | retAddr {loc k} : root loc → AddrCont roots k → Control root roots (.retV (.addr loc) k)
  | store {loc b env k} : root loc → roots env → ReturnCont roots k →
      Control root roots (.next (.storeK [.chain (.addr loc) [] []] [.bool b] (.seqn #[]) env k))
  | storeDone {env k} : roots env → ReturnCont roots k →
      Control root roots (.next (.storeK [] [] (.seqn #[]) env k))
  | returning {k} : ReturnCont roots k → Control root roots (.signal .ret k)

theorem ReturnCont.mono {roots roots' k} (h : ReturnCont roots k)
    (hr : ∀ env, roots env → roots' env) : ReturnCont roots' k := by
  induction h with
  | barrier => exact .barrier
  | seq hc he hs _ ih => exact .seq hc (hr _ he) hs ih

theorem BoolCont.mono {root root' roots roots' k} (h : BoolCont root roots k)
    (hl : ∀ loc, root loc → root' loc) (hr : ∀ env, roots env → roots' env) :
    BoolCont root' roots' k := by
  induction h with
  | not he _ ih => exact .not (hr _ he) ih
  | and hc he ht _ ih => exact .and hc (hr _ he) ht ih
  | or hc he ht _ ih => exact .or hc (hr _ he) ht ih
  | coerce _ ih => exact .coerce ih
  | branch hc he ht hf hk => exact .branch hc (hr _ he) ht hf (hk.mono hr)
  | rhs hl' he hk => exact .rhs (hl _ hl') (hr _ he) (hk.mono hr)

theorem AddrCont.mono {roots roots' k} (h : AddrCont roots k)
    (hr : ∀ env, roots env → roots' env) : AddrCont roots' k := by
  cases h with
  | target hc he ht hk => exact .target hc (hr _ he) ht (hk.mono hr)

theorem Control.mono {root root' roots roots' c} (h : Control root roots c)
    (hl : ∀ loc, root loc → root' loc) (hr : ∀ env, roots env → roots' env) :
    Control root' roots' c := by
  cases h with
  | terminal => exact .terminal
  | next hk => exact .next (hk.mono hr)
  | exec hc he hs hk => exact .exec hc (hr _ he) hs (hk.mono hr)
  | execSeq hc he hs ht hk => exact .execSeq hc (hr _ he) hs ht (hk.mono hr)
  | evalBool hc he ht hk => exact .evalBool hc (hr _ he) ht (hk.mono hl hr)
  | evalRef hc he hn hk => exact .evalRef hc (hr _ he) hn (hk.mono hr)
  | retBool hk => exact .retBool (hk.mono hl hr)
  | retAddr hl' hk => exact .retAddr (hl _ hl') (hk.mono hr)
  | store hl' he hk => exact .store (hl _ hl') (hr _ he) (hk.mono hr)
  | storeDone he hk => exact .storeDone (hr _ he) (hk.mono hr)
  | returning hk => exact .returning (hk.mono hr)

/-- Entering a nested sequence under an already typed continuation.
Same-environment splicing uses a union context and weakening, not equality
between static scope lists or an assumption that future names exist now. -/
theorem control_seqCont {root roots Γ ss env k}
    (hc : Covers Γ env) (he : roots env) (hs : ControlStmts Γ ss)
    (hk : ReturnCont roots k) : Control root roots (.next (seqCont ss env k)) := by
  cases hk with
  | barrier => exact .next (.seq hc he hs .barrier)
  | @seq Δ env' rest k hc' he' ht hk =>
      simp only [seqCont]
      split
      next heq =>
        subst env'
        let Ξ := Γ ++ Δ
        have hss := hs.weaken Ξ (Included.append_left Γ Δ)
        have hrest := ht.weaken (afterStmts Ξ ss)
          ((Included.append_right Γ Δ).trans (afterStmts_extends Ξ ss))
        exact .next (.seq (hc.append hc') he
          ((controlStmts_append_iff Ξ ss rest).mpr ⟨hss, hrest⟩) hk)
      next => exact .next (.seq hc he hs (.seq hc' he' ht hk))

theorem ReturnCont.not_stop {roots} : ¬ ReturnCont roots .stop := by
  intro h
  cases h

theorem Control.not_return_stop {root roots} :
    ¬ Control root roots (.signal .ret .stop) := by
  intro h
  cases h with
  | returning hk => exact hk.not_stop

/-- The placement flag is discharged by an actual control/environment
equation, rather than being treated as an execution-safety premise. -/
theorem Control.initialization_environment {root roots p env rest env' k}
    (h : Control root roots (.exec (.initialization p) env (.seq rest env' k))) :
    env = env' := by
  cases h with
  | exec _ _ hs _ => cases hs
  | execSeq => rfl

theorem Control.initialization_not_barrier {root roots p env} :
    ¬ Control root roots (.exec (.initialization p) env (.frame [] [] [] [] .stop)) := by
  intro h
  cases h with
  | exec _ _ hs _ => cases hs

theorem Control.not_panicking {root roots chain k} :
    ¬ Control root roots (.panicking chain k) := by
  intro h
  cases h

end GoLean.GoCore.BooleanRuntime
