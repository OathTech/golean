import GoLeanProofs.SliceMem
import GoLeanProofs.Specs.Raft.AbsStateV2
import GoLeanProofs.Specs.Raft.Bf31

/-! # A4-U13 census: becomeLeader at the born-re-sited fixture
(state = 1 candidate, term-equal reset — the bf31 spine + the
appendEntry tail). THE CENSUS'S POINT (coordinator-confirmed): walk
the inter-spill segments looking for a CAP-consuming re-read of a
spilled handle — len-shaped reads are choice-independent (the la_len
class); anything else is the finding. -/

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym GoLean.Surface
  GoLean.Frame GoLean.RaftSeam

def shBfc' : Nat → Nat := fun x => if x == 18 || x == 19 then x else x + 31

def blHeap : GoCore.Heap :=
  (uHeap 7 2 1 5).map (fun (l, c) =>
    (renameLoc shBfc' l, ⟨c.declaredTy, renameValue shBfc' c.value⟩))

def blσ0 : ExecState := { wBase with heap := blHeap, nextAddr := 52 }

def blC0 : Machine.Config :=
  .retV (.addr (.base ⟨31⟩))
    (.callArgsK ⟨"raft.raft.becomeLeader"⟩ [] [] [] [] .stop)

def bigStream : Choices := [3, 1, 0, 0] ++ List.replicate 56 0

partial def findStop (n : Nat) : Nat :=
  if n > 30000 then 0
  else match stepFnIter n blσ0 blC0 bigStream with
    | .ok (Machine.Config.next .stop, _, _) => n
    | .error _ => n + 1000000
    | _ => findStop (n + 1)
def nStop := findStop 600
#eval s!"completion at step {nStop}"

#eval match stepFnIter nStop blσ0 blC0 bigStream with
  | .ok (_, σ', ch) =>
      let maaStr : String := "msgsAfterAppend"
      let msgsStr : String := "msgs"
      s!"choices={60 - ch.length} na={σ'.nextAddr}\n" ++
      s!"msgsAfterAppend={(toString (repr (absOutbox σ' ⟨31⟩ maaStr))).take 420}\n" ++
      s!"msgs={(toString (repr (absOutbox σ' ⟨31⟩ msgsStr))).take 120}\n" ++
      s!"absRaftLog post={(toString (repr (absRaftLog σ' ⟨32⟩))).take 320}\n" ++
      s!"absRaftNode post={(toString (repr (absRaftNode σ' ⟨31⟩))).take 200}"
  | .error e => s!"ERROR {e.status}: {e.message.take 200}"

partial def findPops (n : Nat) (last : Nat) (acc : List Nat) : List Nat :=
  if n > nStop then acc.reverse
  else match stepFnIter n blσ0 blC0 bigStream with
    | .ok (_, _, ch) =>
        if 60 - ch.length > last then findPops (n+1) (60 - ch.length) ((n-1) :: acc)
        else findPops (n+1) last acc
    | _ => acc.reverse
#eval s!"choice-consumption step indices: {toString (repr (findPops 600 0 []))}"

/-! ## The mirror walk with automated quit classification. -/

def blSymHeap : List (Loc × GoLean.Sym.HeapCell symDom) :=
  blHeap.map (fun (l, c) => (l, .mk c.declaredTy (embedGo c.value)))
def blS0 : SymState := { heap := blSymHeap, nextAddr := 52 }
def blC0sym : SymConfig :=
  .retV (.addr (.base ⟨31⟩))
    (.callArgsK ⟨"raft.raft.becomeLeader"⟩ [] [] [] [] .stop)

partial def walkMirror (S : SymState) (C : SymConfig)
    (pickVars : List (Nat × IntKind)) (nextAtom : Nat)
    (acc : List String) (rounds : Nat) : List String :=
  if rounds = 0 then ("OUT OF ROUNDS" :: acc).reverse
  else
    let (n, S', C') := symEvalWindowTB bfTB 30000 S C
    match C' with
    | .next .stop => (s!"win {n} → STOP" :: acc).reverse
    | .next (.mapIterK ko vo kt vt body base produced start env k) =>
        -- pick or range-stop? if machine consumed a choice here it's a pick;
        -- classify by whether candidates remain: use pickVars budget — cross
        -- as PICK if vars remain matching, else STOP; report both options.
        (match pickVars with
         | (v, kind) :: rest =>
            -- try pick first
            let (S2, C2) := uCrossPick v kind S'
              (.next (.mapIterK ko vo kt vt body base produced start env k))
            walkMirror S2 C2 rest nextAtom
              (s!"win {n} → PICK(var {v})" :: acc) (rounds - 1)
         | [] =>
            let (S2, C2) := uCrossStop S'
              (.next (.mapIterK ko vo kt vt body base produced start env k))
            walkMirror S2 C2 [] nextAtom
              (s!"win {n} → RANGE-STOP" :: acc) (rounds - 1))
    | .retV (GoLean.Sym.Value.slice sv) (.stmtOpK (.sortSlice ty) nt done pending env k) =>
        let (S2, C2) := uCrossSort S'
          (.retV (.slice sv) (.stmtOpK (.sortSlice ty) nt done pending env k))
        walkMirror S2 C2 pickVars nextAtom (s!"win {n} → SORT" :: acc) (rounds - 1)
    | .retV (GoLean.Sym.Value.slice sv) (.stmtOpK (.appendSlice ty) _ done _ _ k) =>
        (match done with
         | [_, GoLean.Sym.Value.addr (.base tgt)] =>
            let S2 : SymState :=
              { heap := (GoLean.Sym.Heap.set S'.heap (.base tgt)
                  (.mk (some (.slice ty)) (.atom nextAtom))) ++
                  [(.base ⟨S'.nextAddr⟩, .atom nextAtom)],
                nextAddr := S'.nextAddr + 1 }
            walkMirror S2 (.next k) pickVars (nextAtom + 1)
              (s!"win {n} → SPILL(atom {nextAtom}, ty {(toString (repr ty)).take 50}, tgt {tgt.id}, elems {(toString (repr sv.base)).take 40}, backing {S'.nextAddr})" :: acc)
              (rounds - 1)
         | _ => (s!"win {n} → SPILL odd operands" :: acc).reverse)
    | .retV (GoLean.Sym.Value.atom a) (.strictK (.lengthOf ty) [] [] _ k) =>
        walkMirror S' (.retV (.int (.lit 1) .int) k) pickVars nextAtom
          (s!"win {n} → LEN(atom {a}) := 1" :: acc) (rounds - 1)
    | .retV (GoLean.Sym.Value.atom a) k2 =>
        (s!"win {n} → ATOM-READ NOT LEN (atom {a}): THE WATCH-ITEM? cont head: {(toString (repr (match k2 with | .strictK op _ _ _ _ => toString (repr op) | .stmtOpK op _ _ _ _ _ => toString (repr op) | _ => "other"))).take 150}" :: acc).reverse
    | .exec st _ _ =>
        (s!"win {n} → EXEC quit: {(toString (repr st)).take 250}" :: acc).reverse
    | .evalE e _ _ =>
        (s!"win {n} → EVALE quit: {(toString (repr e)).take 250}" :: acc).reverse
    | .retV _ (.stmtOpK op _ _ _ _ _) =>
        (s!"win {n} → stmtOpK quit: {(toString (repr op)).take 120}" :: acc).reverse
    | .retV _ (.strictK op _ _ _ _) =>
        (s!"win {n} → strictK quit: {(toString (repr op)).take 120}" :: acc).reverse
    | _ => (s!"win {n} → OTHER quit" :: acc).reverse

#eval show IO Unit from do
  let segs := walkMirror blS0 blC0sym
    [(5, .int), (6, .uint64), (7, .uint64), (8, .uint64)] 0 [] 30
  for s in segs do IO.println s
