import GoLeanProofs.FuelMeasure

/-!
# THE PLUG RULE, part 1: the replacement function and the barrier
predicates (W2 unit 1; design note `docs/2026-08-27_w1-judgment-design.md` §7)

`plugK env' k'` replaces the below-barrier context of a continuation:
at THE BARRIER — the unique frame whose tail slot is literally
`.stop`, in the resultless non-wrapper shape a freshly entered
callee frame has at the canonical (empty) caller context — it
substitutes the caller-env slot and the tail; at a
bare `.stop` (reached only outside the barrier's protection: the exit
configuration `.next .stop` and the panic-crossed
`.panicking chain .stop`) it substitutes the tail alone. Everywhere
else it maps over the spine. `Cont` is linear (every constructor has
exactly one tail), so the substitution fires exactly once.

The predicates: `hasBarrierK` (the induction invariant of the
per-step walk — the spine carries a well-shaped barrier),
`mapIterFree` (premise 2 of §7: the plug context carries no in-flight
map-range frame — the delete-prune walk crosses call frames by
design, Machine.lean's `pruneIterFramesKey`, so a callee-side
`mapDelete`/`clearMap` would prune context frames the canonical run
cannot see). Premise 1 (`recoverThroughWrappers k' = none`) is stated
directly on the machine's own walk — no new predicate needed.

LINEAGE (§7): wp_bind / evaluation-context composition
(Iris; Felleisen–Hieb), realized as a per-step commutation of the
context-replacement function with the executable `stepFn`
(certificate-replay style) because the machine's continuations are
defunctionalized. The premises are the non-locality census: Go's
recover walk and live map-range pruning are exactly the machine
features that inspect the context through a call boundary.
-/

namespace GoLean.Frame

open GoLean GoLean.GoCore GoLean.GoCore.Machine

/-- The below-barrier replacement. The FIRST arm is the barrier (the
resultless, non-wrapper frame directly over `.stop` — the canonical
callee-entry shape); the `.stop` arm fires only outside the barrier's
protection (exit / panic-crossed configurations). Everything else is
the spine functor. -/
def plugK (env' : LocalEnv) (k' : Cont) : Cont → Cont
  | .frame [] _te r ds .stop false => .frame [] env' r ds k' false
  | .stop => k'
  | .seq a b k => .seq a b (plugK env' k' k)
  | .loop a b c k => .loop a b c (plugK env' k' k)
  | .frame t te r ds k w => .frame t te r ds (plugK env' k' k) w
  | .deferCalleeK a b k => .deferCalleeK a b (plugK env' k' k)
  | .deferArgsK a b c d k => .deferArgsK a b c d (plugK env' k' k)
  | .breakableK k => .breakableK (plugK env' k' k)
  | .labelK a k => .labelK a (plugK env' k' k)
  | .callValCalleeK a b c k => .callValCalleeK a b c (plugK env' k' k)
  | .callValArgsK a b c d e k => .callValArgsK a b c d e (plugK env' k' k)
  | .strictK a b c d k => .strictK a b c d (plugK env' k' k)
  | .andK a b k => .andK a b (plugK env' k' k)
  | .orK a b k => .orK a b (plugK env' k' k)
  | .boolK k => .boolK (plugK env' k' k)
  | .ifK a b c k => .ifK a b c (plugK env' k' k)
  | .whileK a b c k => .whileK a b c (plugK env' k' k)
  | .callArgsK a b c d e k => .callArgsK a b c d e (plugK env' k' k)
  | .stmtOpK a b c d e k => .stmtOpK a b c d e (plugK env' k' k)
  | .mapRangeK a b c d e f k => .mapRangeK a b c d e f (plugK env' k' k)
  | .mapIterK a b c d e f g h i k => .mapIterK a b c d e f g h i (plugK env' k' k)
  | .panicArgK k => .panicArgK (plugK env' k' k)
  | .panicResumeK a k => .panicResumeK a (plugK env' k' k)
  | .chanStK a b c d k => .chanStK a b c d (plugK env' k' k)
  | .selectOpsK a b c d e k => .selectOpsK a b c d e (plugK env' k' k)
  | .tgtOpK a b c d e f g h i j k => .tgtOpK a b c d e f g h i j (plugK env' k' k)
  | .rhsK a b c d e f k => .rhsK a b c d e f (plugK env' k' k)
  | .storeK a b c d k => .storeK a b c d (plugK env' k' k)
  | .goCalleeK a b k => .goCalleeK a b (plugK env' k' k)
  | .goArgsK a b c d k => .goArgsK a b c d (plugK env' k' k)
  | .syncStK a b c d k => .syncStK a b c d (plugK env' k' k)

/-- The spine carries a WELL-SHAPED barrier: a resultless
(`targets = []`), non-wrapper frame directly over `.stop`. An
ill-shaped frame over `.stop` (targeted, or wrapper) refutes — the
plug rule does not apply there (§7 premise 3 and the resultless
scope). -/
def hasBarrierK : Cont → Bool
  | .frame [] _ _ _ .stop false => true
  | .frame _ _ _ _ k _ => hasBarrierK k
  | .stop => false
  | .seq _ _ k => hasBarrierK k
  | .loop _ _ _ k => hasBarrierK k
  | .deferCalleeK _ _ k => hasBarrierK k
  | .deferArgsK _ _ _ _ k => hasBarrierK k
  | .breakableK k => hasBarrierK k
  | .labelK _ k => hasBarrierK k
  | .callValCalleeK _ _ _ k => hasBarrierK k
  | .callValArgsK _ _ _ _ _ k => hasBarrierK k
  | .strictK _ _ _ _ k => hasBarrierK k
  | .andK _ _ k => hasBarrierK k
  | .orK _ _ k => hasBarrierK k
  | .boolK k => hasBarrierK k
  | .ifK _ _ _ k => hasBarrierK k
  | .whileK _ _ _ k => hasBarrierK k
  | .callArgsK _ _ _ _ _ k => hasBarrierK k
  | .stmtOpK _ _ _ _ _ k => hasBarrierK k
  | .mapRangeK _ _ _ _ _ _ k => hasBarrierK k
  | .mapIterK _ _ _ _ _ _ _ _ _ k => hasBarrierK k
  | .panicArgK k => hasBarrierK k
  | .panicResumeK _ k => hasBarrierK k
  | .chanStK _ _ _ _ k => hasBarrierK k
  | .selectOpsK _ _ _ _ _ k => hasBarrierK k
  | .tgtOpK _ _ _ _ _ _ _ _ _ _ k => hasBarrierK k
  | .rhsK _ _ _ _ _ _ k => hasBarrierK k
  | .storeK _ _ _ _ k => hasBarrierK k
  | .goCalleeK _ _ k => hasBarrierK k
  | .goArgsK _ _ _ _ k => hasBarrierK k
  | .syncStK _ _ _ _ k => hasBarrierK k

/-- No in-flight `mapIterK` frame anywhere in the spine (§7 premise 2
— the delete-prune identity condition on the plug context). -/
def mapIterFree : Cont → Bool
  | .mapIterK _ _ _ _ _ _ _ _ _ _ => false
  | .stop => true
  | .seq _ _ k => mapIterFree k
  | .loop _ _ _ k => mapIterFree k
  | .frame _ _ _ _ k _ => mapIterFree k
  | .deferCalleeK _ _ k => mapIterFree k
  | .deferArgsK _ _ _ _ k => mapIterFree k
  | .breakableK k => mapIterFree k
  | .labelK _ k => mapIterFree k
  | .callValCalleeK _ _ _ k => mapIterFree k
  | .callValArgsK _ _ _ _ _ k => mapIterFree k
  | .strictK _ _ _ _ k => mapIterFree k
  | .andK _ _ k => mapIterFree k
  | .orK _ _ k => mapIterFree k
  | .boolK k => mapIterFree k
  | .ifK _ _ _ k => mapIterFree k
  | .whileK _ _ _ k => mapIterFree k
  | .callArgsK _ _ _ _ _ k => mapIterFree k
  | .stmtOpK _ _ _ _ _ k => mapIterFree k
  | .mapRangeK _ _ _ _ _ _ k => mapIterFree k
  | .panicArgK k => mapIterFree k
  | .panicResumeK _ k => mapIterFree k
  | .chanStK _ _ _ _ k => mapIterFree k
  | .selectOpsK _ _ _ _ _ k => mapIterFree k
  | .tgtOpK _ _ _ _ _ _ _ _ _ _ k => mapIterFree k
  | .rhsK _ _ _ _ _ _ k => mapIterFree k
  | .storeK _ _ _ _ k => mapIterFree k
  | .goCalleeK _ _ k => mapIterFree k
  | .goArgsK _ _ _ _ k => mapIterFree k
  | .syncStK _ _ _ _ k => mapIterFree k

/-- The configuration-level plug: map `plugK` over the carried
continuation (through `opDone`'s inner configuration; `.panicked` has
no continuation). -/
def plugC (env' : LocalEnv) (k' : Cont) : Config → Config
  | .exec s e k => .exec s e (plugK env' k' k)
  | .evalE e env k => .evalE e env (plugK env' k' k)
  | .retV v k => .retV v (plugK env' k' k)
  | .next k => .next (plugK env' k' k)
  | .breaking k => .breaking (plugK env' k' k)
  | .continuing k => .continuing (plugK env' k' k)
  | .returning k => .returning (plugK env' k' k)
  | .breakingTo l k => .breakingTo l (plugK env' k' k)
  | .continuingTo l k => .continuingTo l (plugK env' k' k)
  | .panicking chain k => .panicking chain (plugK env' k' k)
  | .panicked msg => .panicked msg
  | .blockedSend c v k => .blockedSend c v (plugK env' k' k)
  | .blockedRecv c t e env k => .blockedRecv c t e env (plugK env' k' k)
  | .blockedSelect cl env k => .blockedSelect cl env (plugK env' k' k)
  | .opDone sched inner => .opDone sched (plugC env' k' inner)
  | .blockedSync op l env k => .blockedSync op l env (plugK env' k' k)

/-- The configuration-level barrier invariant (through `opDone`;
`.panicked` refutes). -/
def hasBarrierC : Config → Bool
  | .exec _ _ k => hasBarrierK k
  | .evalE _ _ k => hasBarrierK k
  | .retV _ k => hasBarrierK k
  | .next k => hasBarrierK k
  | .breaking k => hasBarrierK k
  | .continuing k => hasBarrierK k
  | .returning k => hasBarrierK k
  | .breakingTo _ k => hasBarrierK k
  | .continuingTo _ k => hasBarrierK k
  | .panicking _ k => hasBarrierK k
  | .panicked _ => false
  | .blockedSend _ _ k => hasBarrierK k
  | .blockedRecv _ _ _ _ k => hasBarrierK k
  | .blockedSelect _ _ k => hasBarrierK k
  | .opDone _ inner => hasBarrierC inner
  | .blockedSync _ _ _ k => hasBarrierK k

end GoLean.Frame
