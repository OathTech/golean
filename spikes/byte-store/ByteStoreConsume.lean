import ByteStore

namespace GoLean.GoCore.ByteStorePrototype

/-- Bounded consuming variant. `modifyM` releases the old heap-cell slot
before running its callback in Lean's standard compiled implementation.
Other root shapes fail visibly; the certificate excludes these branches. -/
def consumeByteElement (state : ExecState) (a : Addr) (index : Int)
    (v : GoValue) : Except Stop ExecState :=
  match state with
  | ⟨types, functions, methods, methodSets, typeDisplays, heap⟩ => do
    if a.id < heap.size then
      let heap ← heap.modifyM a.id fun
        | .value (.array n (.int .uint8)) (.array values) => do
          let updated ← setByte values index v
          pure (.value (.array n (.int .uint8)) (.array updated))
        | _ => stuck "byte-store prototype: expected a declared byte-array root"
      pure ⟨types, functions, methods, methodSets, typeDisplays, heap⟩
    else stuck s!"unbound GoCore heap location: {repr (Loc.base a)}"

theorem consumeByteElement_eq (state : ExecState) (a : Addr) (index : Int)
    (v : GoValue) {n : Nat} {values : Array GoValue}
    (hc : Heap.lookup state.heap (.base a) =
      some (.value (.array n (.int .uint8)) (.array values))) :
    consumeByteElement state a index v = storeByteElement state a index v := by
  have ha := Heap.lookup_lt hc
  have hget := (Array.getElem?_eq_some_iff.mp hc).2
  cases state with
  | mk types functions methods methodSets typeDisplays heap =>
    simp only [consumeByteElement, ha, ↓reduceIte, Array.modifyM, ↓reduceDIte,
      hget, storeByteElement, hc]
    cases setByte values index v <;>
      simp [ExecState.updateCell, ha, Bind.bind, Except.bind, pure, Except.pure,
        Functor.map, Except.map]

theorem consumeByteElement_eq_storeLoc (state : ExecState) (a : Addr) (index : Int)
    (v : GoValue) {n : Nat} {values : Array GoValue}
    (hc : Heap.lookup state.heap (.base a) =
      some (.value (.array n (.int .uint8)) (.array values)))
    (hn : BackingNormal n values) :
    consumeByteElement state a index v = storeLoc state (.index (.base a) index) v :=
  (consumeByteElement_eq state a index v hc).trans
    (storeByteElement_eq_storeLoc state a index v hc hn)

def consumeCertifiedByteElement {a : Addr} {n : Nat}
    (state : { s : ExecState // NormalBackingAt s a n })
    (index : Int) (v : GoValue) : Except Stop { s : ExecState // NormalBackingAt s a n } :=
  match hs : consumeByteElement state.val a index v with
  | .error e => .error e
  | .ok state' => .ok ⟨state', by
    obtain ⟨values, hc, hn⟩ := state.property
    exact storeByteElement_preserves state.property index v
      ((consumeByteElement_eq state.val a index v hc).symm.trans hs)⟩

theorem consumeCertifiedByteElement_eq_storeLoc {a : Addr} {n : Nat}
    (state : { s : ExecState // NormalBackingAt s a n }) (index : Int) (v : GoValue) :
    (consumeCertifiedByteElement state index v).map Subtype.val =
      storeLoc state.val (.index (.base a) index) v := by
  obtain ⟨values, hc, hn⟩ := state.property
  rw [← consumeByteElement_eq_storeLoc state.val a index v hc hn]
  unfold consumeCertifiedByteElement
  split <;> rename_i result hr <;> exact hr.symm

end GoLean.GoCore.ByteStorePrototype
