import GoLean.GoCore.BridgeSet
open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Semantics

-- (a) the pin of row 3 with `n ≤ fuel` mutated to `n < fuel`: must FAIL
example : ∀ {ctx : ProgramCtx} {fuel : Nat} {s : Store} {c : Config} {ch : Choices} {sf : Store}
    {chf : Choices},
    execStmtLoop ctx fuel s c ch = .ok (sf, chf) ↔
      ∃ n, n < fuel ∧ Trace ctx n s c ch sf (.next .stop) chf :=
  @GoLean.Semantics.run_ok_iff

-- (b) a drifted (weakened) theorem pinned at the ORIGINAL row-4 type: must FAIL
theorem erase_drifted {ctx : ProgramCtx} {n : Nat} {s : Store} {c : Config} {ch : Choices}
    {sf : Store} {cf : Config} {chf : Choices} (h : Trace ctx n s c ch sf cf chf) (_extra : n = 0) :
    Steps ctx c s cf sf := Trace.erase h
example : ∀ {ctx : ProgramCtx} {n : Nat} {s : Store} {c : Config} {ch : Choices} {sf : Store}
    {cf : Config} {chf : Choices},
    Trace ctx n s c ch sf cf chf → Steps ctx c s cf sf := @erase_drifted

-- (c) the device's stated LIMIT: a same-type definition with different semantics PASSES
def execStmtLoop_changed (ctx : ProgramCtx) (_ : Nat) (s : Store) (_ : Config) (ch : Choices) :
    Except Stop (Store × Choices) := .ok (s, ch)
example : ProgramCtx → Nat → Store → Config → Choices → Except Stop (Store × Choices) :=
  @execStmtLoop_changed
