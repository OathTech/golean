import VerdiCompat.StructTactPrelude

/-!
# Verdi system-model core

1:1 port of the slice of `deps/verdi/theories/Core/Net.v` that the Raft
spec and its headline theorems depend on: the parameter classes, the
packet/network state, and the `step_async` / `step_dup` / `step_drop` /
`step_failure` relations with their trace closures. Skipped on purpose
(not needed by Raft safety/linearizability): disk-op semantics, ordered
per-channel semantics, dynamic-membership semantics, name overlays,
Cheerios serialization.

Mapping decisions (recorded in the design note):
- Coq typeclasses → Lean classes; sumbool deciders → `DecidableEq`
  fields registered as instances.
- Coq's left-associated tuples `A * B * C` → Lean's right-associated
  `A × B × C`; the components and their order are identical.
- `packet`/`network`/step relations take their `MultiParams` instance as
  an EXPLICIT parameter (Coq keeps them section-implicit) so the Raft
  instantiation can name them without instance-resolution tricks.
-/

namespace VerdiCompat

/-- `Net.v:12-17` -/
class BaseParams where
  data : Type
  input : Type
  output : Type

/-- `Net.v:19-23` — the single-node state machine that Raft replicates. -/
class OneNodeParams (P : BaseParams) where
  init : P.data
  handler : P.input → P.data → P.output × P.data

/-- `Net.v:31-43` -/
class MultiParams (P : BaseParams) where
  name : Type
  msg : Type
  [msg_eq_dec : DecidableEq msg]
  [name_eq_dec : DecidableEq name]
  nodes : List name
  all_names_nodes : ∀ n, n ∈ nodes
  no_dup_nodes : nodes.Nodup
  init_handlers : name → P.data
  net_handlers : name → name → msg → P.data →
    List P.output × P.data × List (name × msg)
  input_handlers : name → P.input → P.data →
    List P.output × P.data × List (name × msg)

@[reducible] instance {P : BaseParams} (M : MultiParams P) : DecidableEq M.msg :=
  M.msg_eq_dec
@[reducible] instance {P : BaseParams} (M : MultiParams P) : DecidableEq M.name :=
  M.name_eq_dec

/-- `Net.v:45-48` -/
class FailureParams {P : BaseParams} (M : MultiParams P) where
  reboot : P.data → P.data

/-- `Net.v:103` -/
def step_relation (A trace : Type) := A → A → List trace → Prop

/-- `Net.v:105-110` -/
inductive refl_trans_1n_trace {A trace : Type} (step : step_relation A trace) :
    step_relation A trace
  | RT1nTBase : ∀ x, refl_trans_1n_trace step x x []
  | RT1nTStep : ∀ x x' x'' cs cs',
      step x x' cs →
      refl_trans_1n_trace step x' x'' cs' →
      refl_trans_1n_trace step x x'' (cs ++ cs')

section StepOne
variable (P : BaseParams) (O : OneNodeParams P)

/-- `Net.v:286-290` (`step_1`): the sequential reference semantics of the
single-node machine — the right-hand side of Verdi's linearizability
statement. Note the trace element is a PAIR `input × output`, unlike the
network traces' sum type. -/
inductive step_1 : step_relation P.data (P.input × P.output)
  | S1T_deliver : ∀ (i : P.input) s s' (out : P.output),
      O.handler i s = (out, s') →
      step_1 s s' [(i, out)]

/-- `Net.v:291` -/
def step_1_star := refl_trans_1n_trace (step_1 P O)

end StepOne

section StepAsync
variable (P : BaseParams) (M : MultiParams P)

/-- `Net.v:310-312` -/
structure Packet where
  pSrc : M.name
  pDst : M.name
  pBody : M.msg

/-- `Net.v:320-321`. `nwPackets` is an unordered bag: delivery picks any
`p` with `nwPackets = xs ++ p :: ys`. -/
structure Network where
  nwPackets : List (Packet P M)
  nwState : M.name → P.data

variable {P M}

/-- `Net.v:314` -/
def send_packets (src : M.name) (ps : List (M.name × M.msg)) : List (Packet P M) :=
  ps.map fun m => ⟨src, m.1, m.2⟩

theorem send_packets_app (src : M.name) (l₁ l₂ : List (M.name × M.msg)) :
    send_packets (P := P) src (l₁ ++ l₂) = send_packets src l₁ ++ send_packets src l₂ := by
  simp [send_packets]

@[simp] theorem mem_send_packets_singleton {src dst : M.name} {m : M.msg}
    {q : Packet P M} : q ∈ send_packets src [(dst, m)] ↔ q = ⟨src, dst, m⟩ := by
  simp [send_packets]

@[simp] theorem send_packets_nil (src : M.name) :
    send_packets (P := P) src [] = [] := rfl

variable (P M)

/-- `Net.v:323-324` -/
def step_async_init : Network P M :=
  ⟨[], M.init_handlers⟩

/-- The trace element type: externally visible I/O only (`Net.v:326`). -/
abbrev NetTrace := M.name × (P.input ⊕ List P.output)

/-- `Net.v:326-338` -/
inductive step_async : step_relation (Network P M) (NetTrace P M)
  | StepAsync_deliver : ∀ (net net' : Network P M) (p : Packet P M) xs ys out d l,
      net.nwPackets = xs ++ p :: ys →
      M.net_handlers p.pDst p.pSrc p.pBody (net.nwState p.pDst) = (out, d, l) →
      net' = ⟨send_packets p.pDst l ++ xs ++ ys,
              update net.nwState p.pDst d⟩ →
      step_async net net' [(p.pDst, .inr out)]
  | StepAsync_input : ∀ h (net net' : Network P M) out inp d l,
      M.input_handlers h inp (net.nwState h) = (out, d, l) →
      net' = ⟨send_packets h l ++ net.nwPackets,
              update net.nwState h d⟩ →
      step_async net net' [(h, .inl inp), (h, .inr out)]

/-- `Net.v:340` -/
def step_async_star := refl_trans_1n_trace (step_async P M)

/-- `Net.v:370-387` — `step_async` + duplication of any in-flight packet. -/
inductive step_dup : step_relation (Network P M) (NetTrace P M)
  | StepDup_deliver : ∀ (net net' : Network P M) (p : Packet P M) xs ys out d l,
      net.nwPackets = xs ++ p :: ys →
      M.net_handlers p.pDst p.pSrc p.pBody (net.nwState p.pDst) = (out, d, l) →
      net' = ⟨send_packets p.pDst l ++ xs ++ ys,
              update net.nwState p.pDst d⟩ →
      step_dup net net' [(p.pDst, .inr out)]
  | StepDup_input : ∀ h (net net' : Network P M) out inp d l,
      M.input_handlers h inp (net.nwState h) = (out, d, l) →
      net' = ⟨send_packets h l ++ net.nwPackets,
              update net.nwState h d⟩ →
      step_dup net net' [(h, .inl inp), (h, .inr out)]
  | StepDup_dup : ∀ (net net' : Network P M) (p : Packet P M) xs ys,
      net.nwPackets = xs ++ p :: ys →
      net' = ⟨p :: xs ++ p :: ys, net.nwState⟩ →
      step_dup net net' []

/-- `Net.v:389` -/
def step_dup_star := refl_trans_1n_trace (step_dup P M)

/-- `Net.v:396-411` — `step_async` + dropping of any in-flight packet. -/
inductive step_drop : step_relation (Network P M) (NetTrace P M)
  | StepDrop_deliver : ∀ (net net' : Network P M) (p : Packet P M) xs ys out d l,
      net.nwPackets = xs ++ p :: ys →
      M.net_handlers p.pDst p.pSrc p.pBody (net.nwState p.pDst) = (out, d, l) →
      net' = ⟨send_packets p.pDst l ++ xs ++ ys,
              update net.nwState p.pDst d⟩ →
      step_drop net net' [(p.pDst, .inr out)]
  | StepDrop_drop : ∀ (net net' : Network P M) (p : Packet P M) xs ys,
      net.nwPackets = xs ++ p :: ys →
      net' = ⟨xs ++ ys, net.nwState⟩ →
      step_drop net net' []
  | StepDrop_input : ∀ h (net net' : Network P M) out inp d l,
      M.input_handlers h inp (net.nwState h) = (out, d, l) →
      net' = ⟨send_packets h l ++ net.nwPackets,
              update net.nwState h d⟩ →
      step_drop net net' [(h, .inl inp), (h, .inr out)]

/-- `Net.v:413` -/
def step_drop_star := refl_trans_1n_trace (step_drop P M)

/-- `Net.v:420-454` — the fault model all of verdi-raft's headline theorems
are proved under: deliver/input at live nodes, drop, duplicate, crash,
reboot. State is `(failed set, network)`. -/
inductive step_failure (F : FailureParams M) :
    step_relation (List M.name × Network P M) (NetTrace P M)
  | StepFailure_deliver : ∀ (net net' : Network P M) failed (p : Packet P M) xs ys out d l,
      net.nwPackets = xs ++ p :: ys →
      p.pDst ∉ failed →
      M.net_handlers p.pDst p.pSrc p.pBody (net.nwState p.pDst) = (out, d, l) →
      net' = ⟨send_packets p.pDst l ++ xs ++ ys,
              update net.nwState p.pDst d⟩ →
      step_failure F (failed, net) (failed, net') [(p.pDst, .inr out)]
  | StepFailure_input : ∀ h (net net' : Network P M) failed out inp d l,
      h ∉ failed →
      M.input_handlers h inp (net.nwState h) = (out, d, l) →
      net' = ⟨send_packets h l ++ net.nwPackets,
              update net.nwState h d⟩ →
      step_failure F (failed, net) (failed, net') [(h, .inl inp), (h, .inr out)]
  | StepFailure_drop : ∀ (net net' : Network P M) failed (p : Packet P M) xs ys,
      net.nwPackets = xs ++ p :: ys →
      net' = ⟨xs ++ ys, net.nwState⟩ →
      step_failure F (failed, net) (failed, net') []
  | StepFailure_dup : ∀ (net net' : Network P M) failed (p : Packet P M) xs ys,
      net.nwPackets = xs ++ p :: ys →
      net' = ⟨p :: xs ++ p :: ys, net.nwState⟩ →
      step_failure F (failed, net) (failed, net') []
  | StepFailure_fail : ∀ h (net : Network P M) failed,
      step_failure F (failed, net) (h :: failed, net) []
  | StepFailure_reboot : ∀ h (net net' : Network P M) failed failed',
      h ∈ failed →
      failed' = removeAll h failed →
      net' = ⟨net.nwPackets,
              update net.nwState h (F.reboot (net.nwState h))⟩ →
      step_failure F (failed, net) (failed', net') []

/-- `Net.v:456-457` -/
def step_failure_star (F : FailureParams M) :=
  refl_trans_1n_trace (step_failure P M F)

/-- `Net.v:459` -/
def step_failure_init : List M.name × Network P M :=
  ([], step_async_init P M)

end StepAsync

end VerdiCompat
