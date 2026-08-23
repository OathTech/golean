import GoLeanProofs.Sym.TableExt
import GoLeanProofs.Specs.Raft.BecomeFollowerWitness

/-!
# A4-U2 slice 1, the RE-MEASURE: the pilot leaf's body span, Sym-driven

The pilot's `alt_call_span` (HandlerEq.lean) hand-chained ten windows
across the 15-step `abortLeaderTransfer` call: 1 conditioned
`enterFrame` step + 14 body/store/exit steps carried by per-step kit
haves. THIS module reproduces the 14-step body span as ONE transported
window through `symEvalWindowT` at the pinned type table — the store's
whole-struct re-normalization, the hand proof's cost center, now
COMPUTED by the evaluator instead of conditioned by hand. The
call-enter step is out of the window in both versions (Q4; class 2 of
the design), so the comparison is body-span vs body-span.

The window's pre-state is VALUE-SYMBOLIC, ADDRESS-CONCRETE (design
§5): the raft cell's five pilot scalars are `SymInt` vars, the layout
is the witness layout; the equation quantifies over every valuation ρ,
every table-carrier σ extending the pin's types, and every choice
stream (unchanged — the window consumes no choices).
-/

namespace GoLean.RaftSeam

open GoLean GoLean.GoCore GoLean.GoCore.Machine GoLean.Sym

/-! ## Embedding concrete values into the symbolic domain -/

/-- Fueled embedding of a concrete `GoValue` as a mirror value (every
scalar a literal term). Fuel exhaustion yields an `atom`, which QUITS
on any use — fail closed, never a silent wrong embedding. -/
def embedGoF : Nat → GoValue → SymValue
  | 0, _ => .atom 0
  | _ + 1, .unit => .unit
  | _ + 1, .bool b => .bool (.lit b)
  | _ + 1, .int v k => .int (.lit v) k
  | _ + 1, .float bits k => .float bits k
  | _ + 1, .string s => .string s
  | _ + 1, .addr l => .addr l
  | _ + 1, .nil => .nil
  | fuel + 1, .interface d v => .interface d (embedGoF fuel v)
  | fuel + 1, .struct tid fs =>
      .struct tid (fs.map (fun p => (p.1, embedGoF fuel p.2)))
  | fuel + 1, .array vs => .array (vs.map (embedGoF fuel))
  | _ + 1, .slice sv => .slice sv
  | _ + 1, .map mv => .map mv
  | fuel + 1, .mapData entries =>
      .mapData (entries.map (fun p => (embedGoF fuel p.1, embedGoF fuel p.2)))
  | _ + 1, .chan cv => .chan cv
  | fuel + 1, .chanData buf cap closed =>
      .chanData (buf.map (embedGoF fuel)) cap closed
  | fuel + 1, .funcVal fid captured =>
      .funcVal fid (captured.map (embedGoF fuel))
  | _ + 1, .syncData p => .syncData p

def embedGo (v : GoValue) : SymValue := embedGoF valueEqbFuel v

/-- Replace one named field's payload in a mirror struct value. -/
def setSymField (v : SymValue) (name : String) (nv : SymValue) : SymValue :=
  match v with
  | .struct tid fs =>
      .struct tid (fs.map (fun p => if p.1 == name then (p.1, nv) else p))
  | v => v

/-! ## The window fixture: the witness layout, five scalars symbolic -/

/-- The pinned program's type table (the window's `T`). -/
def twinTypes : TypeEnv := wBase.types

/-- The raft cell's value with the pilot's five scalars symbolic:
`Term ↦ x₀`, `Vote ↦ x₁`, `lead ↦ x₂`, `state ↦ x₃`,
`leadTransferee ↦ x₄`; every other field the machine's own zero value
(embedded from `wRaftVal`). -/
def symRaftVal : SymValue :=
  setSymField
    (setSymField
      (setSymField
        (setSymField
          (setSymField (embedGo wRaftVal) "Term" (.int (.var 0) .uint64))
          "Vote" (.int (.var 1) .uint64))
        "lead" (.int (.var 2) .uint64))
      "state" (.int (.var 3) .uint64))
    "leadTransferee" (.int (.var 4) .uint64)

/-- The post-`enterFrame` symbolic state: raft cell at 0 (symbolic
scalars), raftLog cell at 1, the param cell for `r` at 2. -/
def altS₀ : SymState :=
  { heap := [(.base ⟨0⟩, .mk (some tyRaft) symRaftVal),
             (.base ⟨1⟩, .mk (some tyRaftLog) (embedGo wLogVal)),
             (.base ⟨2⟩, .mk (some (.pointer tyRaft)) (.addr (.base ⟨0⟩)))],
    nextAddr := 3 }

/-- The post-`enterFrame` configuration: the callee body under its
frame, caller continuation `.stop` (window-scoped). -/
def altC₀ : SymConfig :=
  .exec altBody [[("r", .base ⟨2⟩)]] (.frame [] [] [] [] .stop false)

set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000
set_option smartUnfolding false

/-- The window RUNS: 14 completed steps, no quit — in particular the
store's re-normalization of the whole 32-field raft struct (symbolic
scalars included, via `norm` terms) PROCEEDS at the pinned table.
`#eval`-checked before asking the elaborator (the standing rule). -/
theorem alt_sym_window_n :
    (symEvalWindowT twinTypes 14 altS₀ altC₀).1 = 14 := by
  with_unfolding_all rfl

/-- **THE RE-MEASURED SPAN** — the pilot leaf's 14-step body span as
one transported window: ∀ valuation, ∀ table-carrier extending the
pin's types, ∀ choice stream. The output state is the WINDOW'S OWN
(nothing hand-transcribed); the store's normalization was computed,
not conditioned. -/
theorem alt_call_span_sym (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hsub : SubTable twinTypes σ.types) :
    stepFnIter 14 (γS ρ σ altS₀) (γC ρ altC₀) ch
      = .ok (γC ρ (symEvalWindowT twinTypes 14 altS₀ altC₀).2.2,
          γS ρ σ (symEvalWindowT twinTypes 14 altS₀ altC₀).2.1, ch) :=
  symEvalWindowT_refines' alt_sym_window_n ρ σ ch hsub

/-! ## Discharge witness (constitution §3.3) -/

/-- A concrete valuation with distinct scalar values (a live witness,
not the zero point). -/
def ρ₀ : Valuation :=
  { ints := fun i => [7, 3, 2, 1, 5].getD i 0
    bools := fun _ => false
    vals := fun _ => .nil
    cells := fun _ => ⟨none, .nil⟩ }

/-- Every premise of `alt_call_span_sym` discharged at a concrete
valuation and the pinned tables. -/
theorem alt_call_span_sym_witness :
    stepFnIter 14 (γS ρ₀ wBase altS₀) (γC ρ₀ altC₀) []
      = .ok (γC ρ₀ (symEvalWindowT twinTypes 14 altS₀ altC₀).2.2,
          γS ρ₀ wBase (symEvalWindowT twinTypes 14 altS₀ altC₀).2.1, []) :=
  alt_call_span_sym ρ₀ wBase [] (SubTable.of_eq rfl)

/-- The projection readout at the witness valuation: the transported
window's post-state still projects (`absRaftNode` is `some`, with the
symbolic scalars at their ρ₀ values — Term 7, Vote 3, lead 2, state 1
— and the log summary intact), and the `leadTransferee` store left
the projection UNCHANGED. -/
theorem alt_sym_projection :
    absRaftNode (γS ρ₀ wBase
        (symEvalWindowT twinTypes 14 altS₀ altC₀).2.1) ⟨0⟩
      = absRaftNode (γS ρ₀ wBase altS₀) ⟨0⟩
    ∧ absRaftNode (γS ρ₀ wBase altS₀) ⟨0⟩
      = some ⟨7, 3, 2, 1, 0, 0⟩ := by
  -- compiled-`#eval`-checked true first (SymWindowProbe: both sides
  -- `some ⟨7,3,2,1,0,0⟩`); kernel `decide` — the elaborator whnf
  -- route DNFs on the γ-image of the window output (recorded).
  exact ⟨by decide +kernel, by decide +kernel⟩

/-! ## A4-U2 slice-3 RE-MEASURE: the `becomeFollower` prefix window

With classes 1–3 landed, the pilot handler's run from its call
configuration transports as ONE window until the first uncovered
consult — measured at **189 steps**: frame entry (becomeFollower),
the `step`/`tick` funcVal stores and `lead`/`state` field stores,
`reset`'s frame entry, its term/vote branch and four field stores,
`resetRandomizedElectionTimeout`'s and `Intn`'s frame entries, the
mutex LOCK (sync apply + marker strip), and the map-build prologue —
quitting at `Intn`'s `struct{}{}` literal (`buildStructValue` at a
defined type: the Q4-normalize family's next member, the recorded
slice-3 residual; the map-range pick two constructs later is the
DESIGNED Q3 boundary regardless — design §4(ii)). Pre-extension this
prefix costs ~35 hand windows with ~15 conditioned facts at the
pilot's measured 9 lines/step; post-extension it is one `rfl` + one
refinement application over this fixture.

Branch-relevant scalars are concrete (`Term`/`term` 0,
`electionTimeout` 10 — a symbolic branch scalar would Q1-quit at the
`reset` if, the per-branch-window design); non-branched scalars stay
symbolic (`Vote`, `lead`, `leadTransferee` = x₁/x₂/x₄), ∀ρ. -/

def bfRaftVal : SymValue :=
  setSymField (setSymField (setSymField
    (setSymField (embedGo wRaftVal) "Vote" (.int (.var 1) .uint64))
    "lead" (.int (.var 2) .uint64))
    "leadTransferee" (.int (.var 4) .uint64))
    "electionTimeout" (.int (.lit 10) .int)

/-- The pinned-table pack (all four tables = the twin's). -/
def bfTB : SymTables :=
  { types := twinTypes
    functions := GoLean.Examples.RaftTwin.twinLowered.funcs
    methods := GoLean.Examples.RaftTwin.twinLowered.methods
    methodSets := GoLean.Examples.RaftTwin.twinLowered.methodSets }

/-- The fixture: raft cell at 0 (raftLog → 1), the pin's `globalRand`
cell at its static address 18 → a lockedRand struct at 19 with an
unlocked mutex. -/
def bfS₀ : SymState :=
  { heap := [(.base ⟨0⟩, .mk (some tyRaft) bfRaftVal),
             (.base ⟨1⟩, .mk (some tyRaftLog) (embedGo wLogVal)),
             (.base ⟨18⟩, .mk (some (.pointer (.defined ⟨"raft.lockedRand"⟩)))
                (.addr (.base ⟨19⟩))),
             (.base ⟨19⟩, .mk (some (.defined ⟨"raft.lockedRand"⟩))
                (.struct ⟨"raft.lockedRand"⟩ #[("mu", .syncData (.mutex false))]))],
    nextAddr := 20 }

/-- The drained call configuration of `becomeFollower(0, x₂→)` — the
handler-equation entry shape, at the fixture. -/
def bfC₀ : SymConfig :=
  .retV (.int (.lit 0) .uint64)
    (.callArgsK ⟨"raft.raft.becomeFollower"⟩ []
      [.addr (.base ⟨0⟩), .int (.lit 0) .uint64] [] [] .stop)

/-- 189 completed steps (`#eval`-checked first: 189, quit q4Program
at the `struct{}` literal). -/
theorem bf_window_n : (symEvalWindowTB bfTB 189 bfS₀ bfC₀).1 = 189 := by
  with_unfolding_all rfl

/-- **THE RE-MEASURED HANDLER PREFIX**: 189 steps of `becomeFollower`
from its call configuration, one transported window, ∀ρ ∀σ agreeing
with the pinned tables ∀ch. -/
theorem bf_prefix_span (ρ : Valuation) (σ : ExecState) (ch : Choices)
    (hag : bfTB.Agrees σ) :
    stepFnIter 189 (γS ρ σ bfS₀) (γC ρ bfC₀) ch
      = .ok (γC ρ (symEvalWindowTB bfTB 189 bfS₀ bfC₀).2.2,
          γS ρ σ (symEvalWindowTB bfTB 189 bfS₀ bfC₀).2.1, ch) :=
  symEvalWindowTB_refines' bf_window_n ρ σ ch hag

/-- Discharge witness: the premises hold at the pinned base state and
a concrete valuation. -/
theorem bf_prefix_span_witness :
    stepFnIter 189 (γS ρ₀ wBase bfS₀) (γC ρ₀ bfC₀) []
      = .ok (γC ρ₀ (symEvalWindowTB bfTB 189 bfS₀ bfC₀).2.2,
          γS ρ₀ wBase (symEvalWindowTB bfTB 189 bfS₀ bfC₀).2.1, []) :=
  bf_prefix_span ρ₀ wBase [] ⟨rfl, rfl, rfl, rfl⟩

end GoLean.RaftSeam
