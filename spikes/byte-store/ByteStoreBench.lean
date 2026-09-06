import ByteStoreConsume

open GoLean GoLean.GoCore GoLean.GoCore.ByteStorePrototype

def initial (n : Nat) : { s : ExecState // NormalBackingAt s ⟨0⟩ n } :=
  ⟨{ heap := #[.value (.array n (.int .uint8))
      (.array (Array.replicate n (.int 0 .uint8)))] }, by
    refine ⟨Array.replicate n (.int 0 .uint8), rfl, by simp, ?_⟩
    intro v hv
    simp only [Array.toList_replicate, List.mem_replicate] at hv
    rcases hv with ⟨_, rfl⟩
    exact ⟨0, rfl, by decide, by decide⟩⟩

def runOrdinary (n : Nat) : Except Stop ExecState := do
  let mut state := (initial n).val
  for i in [:n] do
    state ← storeLoc state (.index (.base ⟨0⟩) (Int.ofNat i)) (.int 1 .int)
  pure state

def runCertified (n : Nat) : Except Stop ExecState := do
  let mut state := initial n
  for i in [:n] do
    state ← storeCertifiedByteElement state (Int.ofNat i) (.int 1 .int)
  pure state.val

def runConsuming (n : Nat) : Except Stop ExecState := do
  let mut state := initial n
  for i in [:n] do
    state ← consumeCertifiedByteElement state (Int.ofNat i) (.int 1 .int)
  pure state.val

def verify (n : Nat) (state : ExecState) : IO Unit := do
  match Heap.lookup state.heap (.base ⟨0⟩) with
  | some (.value (.array actual (.int .uint8)) (.array values)) =>
      unless actual == n && values.size == n do throw (IO.userError "wrong array length")
      let mut sum := 0
      for value in values do
        match value with
        | .int 1 .uint8 => sum := sum + 1
        | _ => throw (IO.userError "wrong stored value or integer tag")
      IO.println s!"ok length={n} uint8_ones={sum}"
  | _ => throw (IO.userError "wrong resulting heap shape")

def main (args : List String) : IO Unit := do
  let [mode, count] := args | throw (IO.userError "expected mode count")
  let some n := count.toNat? | throw (IO.userError "invalid count")
  unless n == 1024 || n == 4096 do throw (IO.userError "bounded counts are 1024 and 4096")
  let result ← match mode with
    | "ordinary" => pure (runOrdinary n)
    | "certified" => pure (runCertified n)
    | "consuming" => pure (runConsuming n)
    | _ => throw (IO.userError "expected ordinary, certified, or consuming")
  match result with
  | .error e => throw (IO.userError s!"store failed: {repr e}")
  | .ok state => verify n state
