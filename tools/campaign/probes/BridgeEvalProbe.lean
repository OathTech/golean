import GoLeanProofs.Specs.Raft.NativeCheckerBridge

/-! A4-U23 eval-first probe for the bridge pins + witnesses. -/

open GoLean GoLean.GoCore GoLean.RaftSeam.NativeSpec

-- guard candidates
def s3IdxGuard : Expr :=
  .atMostCmp (.var "idx")
    (.fieldGet (.deref (.var "nd") (.defined ⟨"main.twinNode"⟩)) ⟨"main.twinNode"⟩ "applied")
def s3TermGuard : Expr :=
  .lessCmp (.var "trm")
    (.fieldGet (.deref (.var "nd") (.defined ⟨"main.twinNode"⟩)) ⟨"main.twinNode"⟩ "lastTrm")
def s2Guard : Expr :=
  .or (.neqCmp (.int .uint64) (.fieldGet (.var "s") ⟨"main.slot"⟩ "term") (.var "trm"))
      (.neqCmp .string (.fieldGet (.var "s") ⟨"main.slot"⟩ "data") (.var "data"))
def s1Guard : Expr :=
  .and (.var "ok")
    (.neqCmp (.int .uint64) (.var "prev")
      (.fieldGet (.deref (.var "nd") (.defined ⟨"main.twinNode"⟩)) ⟨"main.twinNode"⟩ "id"))

def collectIfCondsF : Nat → Stmt → List Expr
  | 0, _ => []
  | fuel + 1, s =>
      match s with
      | .ifThenElse c t e =>
          c :: (collectIfCondsF fuel t ++ collectIfCondsF fuel e)
      | .block _ ss => ss.toList.flatMap (collectIfCondsF fuel)
      | .seqn ss => ss.toList.flatMap (collectIfCondsF fuel)
      | .while _ b => collectIfCondsF fuel b
      | .labeled _ b => collectIfCondsF fuel b
      | .breakable b => collectIfCondsF fuel b
      | .mapRange _ _ _ _ _ b => collectIfCondsF fuel b
      | _ => []

def funcIfConds (name : String) : List Expr :=
  match findFunctionIn? GoLean.Examples.RaftTwin.twinLowered.funcs ⟨name⟩ with
  | some f => collectIfCondsF 64 f.body
  | none => []

#eval (funcIfConds "main.twin.apply").length
#eval (funcIfConds "main.twin.apply").any (fun e => Expr.eqbF 4096 e s3IdxGuard)
#eval (funcIfConds "main.twin.apply").any (fun e => Expr.eqbF 4096 e s3TermGuard)
#eval (funcIfConds "main.twin.apply").any (fun e => Expr.eqbF 4096 e s2Guard)
#eval (funcIfConds "main.twin.harvest").length
#eval (funcIfConds "main.twin.harvest").any (fun e => Expr.eqbF 4096 e s1Guard)

-- witness folds
#eval (s1Run [(5,1),(5,2)]).viols          -- expect 1
#eval (s1Run [(5,1),(5,1),(6,1)]).viols    -- expect 0
#eval (s1Run [(5,1),(5,2)]).claims          -- expect 2
def wClean : List AEv :=
  [⟨1,1,2,0⟩,⟨1,2,2,7⟩,⟨1,3,2,8⟩,⟨2,1,2,0⟩,⟨2,2,2,7⟩,⟨2,3,2,8⟩]
#eval ((s23Run wClean).violS2, (s23Run wClean).violS3)   -- expect (0,0)
#eval ((s23Run [⟨1,2,2,7⟩,⟨2,2,2,8⟩]).violS2)            -- expect 1
#eval ((s23Run [⟨1,2,2,7⟩,⟨1,2,2,7⟩]).violS3)            -- expect 1
#eval decide (∀ x ∈ wClean, 1 ≤ x.idx)                    -- expect true
