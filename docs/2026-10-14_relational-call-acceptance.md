# RD3 call/return compatibility and semantic client checks

[USER] 2026-10-14: implement the reusable source-call/return capability in
`golean-logic/.claude/worktrees/relational-demo-brief/docs/2026-10-14_rd3-request-relay.md`.
The six propositions are compatibility obligations, not prescribed exports.
Use corrected delivery and derive result validity from activation. No merge,
push or writes to the logic worktree.

[AGENT] 2026-10-14: add `SavedCaller`, `CallBoundary`, `NormalExit` and
`SavedCaller.invoke` to own call/exit plumbing upstream. Use semantic operand,
binding and ordered-write relations without adding Batteries to production.
Prove root result slots from every successful activation, including repeated
signature identifiers; the detailed layout theorem's distinct-name premise
is unnecessary for this invariant. Move the existing empty-sequence proof to
`RelationalControl` so both assignment and delivery reuse its exact cleanup.

The implementation is in `GoLean/GoCore/RelationalCall.lean`, exported by
`GoLean.Relational`, namespace `GoLean.GoCore.Relational`.

| Obligation | Semantic export / compatibility adapter |
| --- | --- |
| `ReferenceLaw` | `reference` (`Pure`); `RD3Compatibility.reference_law` |
| `AssignVariableLaw` | `assign_variable`; `RD3Compatibility.assignment_law` |
| `CallEntryLaw` | `SavedCaller.enter`; `RD3Compatibility.call_entry_law` |
| `ReturnStartLaw` | `return_start` into `exitPoint .returned`; `RD3Compatibility.return_start_law` |
| `ReturnSequenceLaw` | `return_sequence`; `RD3Compatibility.return_sequence_law` |
| corrected `DeliverLaw` | `CallBoundary.deliver` for either `NormalExit`; `RD3Compatibility.delivery_law` |

`SavedCaller.invoke` composes operand evaluation, declared activation, a
separately proved callee body, readback, ordered destination writes and caller
resumption. `LocalEntry.resultSlots` derives result validity without added
premises. `Readback.traced` bridges ordinary readback to actual labelled frame
reads. `invoke` uses both internally: clients do not supply root validity,
traced reads, target plans, frame constructors or signals.

The fragment is declared non-method calls with store-preserving, pick-free
operands, bound-variable destinations and no pending callee defers. Stores,
values, locations and caller tails in exports are symbolic. Pointer arguments
and caller destinations may be interior; repeated destinations and aliases
with results are allowed. All result values are read before destination
writes, which occur in list order. Actual labels remain ordered in
`PickFreeRun`; only picks are constrained. No observation-silence promise is
added. Operand evaluation need not be output-free. No executable definition,
Step rule, memory operation, choice domain or baseline changed.

The original delivery statement is false for interior pinned result slots:
`loadMany` can read them but `loadResults` refuses them. The relay's checked
counterexample and correction are accepted; no machine behavior was changed
to accommodate malformed frames. The **corrected** six statements below
are all discharged without extra assumptions. The public composed rule
obtains the correction's invariant from activation instead of imposing it
on the client.

## Frozen inputs

Sources were copied read-only from the logic worker before their builds.
The first six files are the exact relay closure; the other six freeze the
existing separately proved Set body and its dependency closure for a further
interface-use check. These latter files are the active RD3 snapshot, not a
claim to reproduce the earlier first-batch hashes. The two relay hashes
match exactly. SHA-256 of each `.lean` file:

```json
{
  "CallRequests": "2571e366b0ecd79a0d65fac6b8506159b0a56bd2a3e0d10aec7e2d0a55912d6b",
  "CallAcceptance": "036ab43e6e1b6fd82384449617275970e769f6bffbeeacfe19dff266bc418a2d",
  "Segments": "e7b2f9c392fb8783f79f7d1ba852f3990c12627706fcd8d2980c769618bee977",
  "Activation": "d3c27ad2ff4588cbbcc6d8a86ac169726cd80906909cbdb6b9b2cafc393e4c79",
  "Control": "f0f2d5933b777c9389332178be8b7c0824e884c496663dd42280486954d2fa25",
  "Fixture": "3f4ec8dd92afa9934b7c8902c97b28736d3a8a12c39cb1fd42fc41d7a9f55c84",
  "Bodies": "c51f71631ff7108dc70efc59be37464089fdc319d7b95d31af2597f7c4fb906e",
  "Supplied": "287618b440d6edce7f6d98e84fdd781ad81398c2d6983f4129a1bfd949beb240",
  "Acceptance": "2bd80dc3cdef81fb3462931bf747b27327c80dda79ea0f5c610576964cafb571",
  "Requests": "b666208139e98d42df1e18d847bd7c53f7239e89a1eb2edf19d5a264cce141b5",
  "Memory": "fac0cf9e80ce7b125cd34217d981052610b628ce735d00c33153e41f9e9a97f8",
  "Boundary": "0df06713a3c34006e58048d6325e99c3e00cac57571f4677d0090b863c774d03"
}
```

Batteries is an independent local clone at
`023ce7d62a0531e22a5331e20b587817a80d49ff`, required by the downstream
`List.Forall₂` request only. Lean is 4.32.2. No Iris imports are used.
No source from this harness is a production upstream dependency.

## Reproduction

Create `.tmp/rd3` under the checked GoLean checkout. Copy each named frozen
file into `.tmp/rd3/RelationalDemo/` and **verify every hash before building**;
if a peer has changed them, obtain the recorded snapshot, do not silently
claim the old input passed. Clone the explicit local Batteries source with
`git clone --no-hardlinks`, into `.tmp/rd3/batteries`, verify its HEAD is the
pin above, and copy the GoLean `lean-toolchain` into `.tmp/rd3`.
Put the following package configuration in `.tmp/rd3/lakefile.toml`:

```toml
name = "rd3-acceptance"
version = "0.1.0"
defaultTargets = ["RelationalDemo", "Compatibility", "SemanticClient"]
[[require]]
name = "golean"
path = "../.."
[[require]]
name = "batteries"
path = "batteries"
[[lean_lib]]
name = "RelationalDemo"
globs = ["RelationalDemo.+"]
[[lean_lib]]
name = "Compatibility"
[[lean_lib]]
name = "SemanticClient"
```

Save the two Lean blocks below as `Compatibility.lean` and
`SemanticClient.lean` in that package. From `.tmp/rd3`:

```sh
LEAN_NUM_THREADS=2 capped lake build
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose GoLean RelationalDemo Compatibility SemanticClient
LEAN_NUM_THREADS=2 capped lake env leanchecker --verbose Batteries
```

Compare `replaying ...` module names to all GoLean sources (including root
`GoLean.lean`), the twelve frozen sources and both harness modules; check
set equality, not just counts. All printed axiom sets must be subsets of
`propext`, `Classical.choice`, `Quot.sound`.

## Exact compatibility proofs

The original request and acceptance files are unchanged. The adapters below
translate their list relations and representation views in scratch; ordinary
client proofs should use the semantic interface directly.

```lean
import RelationalDemo.CallAcceptance
open GoLean GoLean.GoCore GoLean.GoCore.Relational RelationalDemo
namespace RD3Compatibility
private theorem operands {ctx s env es vs}
    (h : CallRequests.Operands ctx s env es vs) : OperandValues ctx s env es vs := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h ih
private theorem bound {env ids ls}
    (h : List.Forall₂ (fun id l => LocalEnv.lookup env id = some l) ids ls) :
    BoundDestinations env ids ls := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h ih
private theorem writes {ctx ls vs s t}
    (h : CallRequests.Writes ctx ls vs s t) : WriteValues ctx ls vs s t := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h ih

theorem reference_law : CallRequests.ReferenceLaw :=
  fun ctx s env k id l h => PickFreeRun.pure (reference ctx s env k id l h)
theorem assignment_law : CallRequests.AssignVariableLaw := assign_variable
theorem return_start_law : CallRequests.ReturnStartLaw :=
  fun ctx s env k => PickFreeRun.pure (return_start ctx s env k)
theorem return_sequence_law : CallRequests.ReturnSequenceLaw :=
  fun ctx s env k rest => PickFreeRun.pure (return_sequence ctx s env k rest)
theorem call_entry_law : CallRequests.CallEntryLaw := by
  intro ctx s caller k ids es vs fid f a ho hf hm ha he
  simpa [Segment, PickFreeRun, SavedCaller.call, CallBoundary.body, SavedCaller.boundary,
    CallBoundary.continuation, CallRequests.callFrame] using
    (SavedCaller.enter ⟨ids.toList, caller, k⟩ (operands ho) hf hm ha he)
theorem delivery_law : CallRequests.DeliverLaw := by
  intro ctx s t caller k ids locs results fid vs hc hv hb hr hw
  let b : CallBoundary := ⟨⟨ids, caller, k⟩, fid, results⟩
  exact ⟨b.deliver .fallthrough hc hv (bound hb) hr (writes hw),
    b.deliver .returned hc hv (bound hb) hr (writes hw)⟩

theorem keep (ctx : ProgramCtx) (s : Store) (env : LocalEnv) (k : Continuation)
    (x arg : Loc) (v : Bool)
    (hx : LocalEnv.lookup env 4 = some x) (ha : LocalEnv.lookup env 0 = some arg)
    (read : loadRoot ctx s arg = .ok (.bool v))
    (found : findFunctionIn? ctx.functions setFunction.id = some setFunction)
    (method : methodInfoByFuncId? ctx setFunction.id = none) :
    Segment ctx (statement (.call #[] setFunction.id #[.ref 4, .var 0]) env k s)
      (statement setFunction.body (setActivation s x v).locals
        (CallRequests.callFrame [] env [] setFunction.id k) (setActivation s x v).store) :=
  CallRequests.keep_call_entry reference_law call_entry_law ctx s env k x arg v hx ha read found method

theorem result (ctx : ProgramCtx) (k : Continuation) (old v : Bool) :
    let s : Store := { heap := #[.value .bool (.bool old), .value .bool (.bool v)] }
    let t : Store := { heap := #[.value .bool (.bool v), .value .bool (.bool v)] }
    let env := LocalEnv.declare [] 7 (.base ⟨0⟩)
    let frame := CallRequests.callFrame [7] env [.base ⟨1⟩] ⟨"Identity"⟩ k
    Segment ctx (resumed frame s) (resumed k t) ∧
      Segment ctx (CallRequests.returnExit frame s) (resumed k t) :=
  CallRequests.one_result_delivery delivery_law ctx k old v
#print axioms reference_law
#print axioms assignment_law
#print axioms return_start_law
#print axioms return_sequence_law
#print axioms call_entry_law
#print axioms delivery_law
#print axioms keep
#print axioms result
end RD3Compatibility
```

## Semantic client composition

This additional check is stronger than the two conditional examples: both
source callers use `SavedCaller.invoke`, with no missing-law parameter.
`keep_set` uses the already proved downstream `set_body` theorem without
reopening it; its write premise remains a semantic operation obligation to
be derived from ownership downstream. `identity_call` proves an actual
nonempty result delivery following a separately proved explicit-return body;
its memory premises reduce for symbolic Boolean values and arbitrary caller
tail. It leaves ordinary function lookup in the supplied context explicit.
These are finite semantic checks, not the completed Iris Keep proof or its
ownership protocol. The Identity test is handwritten GoCore, not a new
lowering certification.

```lean
import RelationalDemo.Bodies
open GoLean GoLean.GoCore GoLean.GoCore.Relational RelationalDemo
namespace RD3SemanticClient

/-- Keep's call uses the separately proved Set contract as a black box. -/
theorem keep_set (ctx : ProgramCtx) (s t : Store) (env : LocalEnv) (k : Continuation)
    (x arg : Loc) (v : Bool)
    (hx : LocalEnv.lookup env 4 = some x) (ha : LocalEnv.lookup env 0 = some arg)
    (read : loadRoot ctx s arg = .ok (.bool v))
    (found : findFunctionIn? ctx.functions setFunction.id = some setFunction)
    (method : methodInfoByFuncId? ctx setFunction.id = none)
    (write : storeLoc ctx (setActivation s x v).store x (.bool v) = .ok t) :
    PickFreeRun ctx ((SavedCaller.mk [] env k).call setFunction.id [.ref 4, .var 0] s)
      (resumed k t) := by
  let caller : SavedCaller := ⟨[], env, k⟩
  have operands : OperandValues ctx s env [.ref 4, .var 0] [.addr x, .bool v] :=
    .cons (fun tail => .pure (reference ctx s env tail 4 x hx))
      (.cons (fun tail => by
        obtain ⟨tr, hr⟩ := read_variable ctx s env tail 0 arg (.bool v) ha read
        exact .single hr rfl) .nil)
  obtain ⟨p, q, hp, hq, rp, rq⟩ := set_entry_arguments ctx s x v
  exact caller.invoke .fallthrough operands found method rfl (set_entry ctx s x v)
    (set_body ctx _ t _ _ p q x v hp hq rp rq write) rfl .nil
    (set_readback ctx s t x v) .nil

/-- Handwritten test input, same source fragment as RD3 Identity; no lowering claim. -/
def identity : Func :=
  { id := ⟨"Identity"⟩, args := #[⟨0, .bool⟩], results := #[⟨1, .bool⟩],
    body := .block #[] #[.assign (.var 1) (.var 0), .returnStmt] }

/-- A separate callee proof using source laws and operation premises. -/
theorem identity_body (ctx : ProgramCtx) (s t : Store) (env : LocalEnv) (k : Continuation)
    (src dst : Loc) (v : Bool)
    (hs : LocalEnv.lookup env 0 = some src) (hd : LocalEnv.lookup env 1 = some dst)
    (read : loadRoot ctx s src = .ok (.bool v)) (write : storeLoc ctx s dst (.bool v) = .ok t) :
    PickFreeRun ctx (statement identity.body env k s) (exitPoint .returned k t) := by
  let inner := env.pushScope
  have start : PickFreeRun ctx (statement identity.body env k s)
      (resumed (sequence [.assign (.var 1) (.var 0), .returnStmt] inner k) s) :=
    .single (block_enter (ctx := ctx) (decls := #[]) (ss := #[.assign (.var 1) (.var 0), .returnStmt])
      (env := env) (env' := inner) (k := k) (s := s) (t := s) rfl).1 rfl
  have assignment := assign_variable ctx s t inner (sequence [.returnStmt] inner k)
    1 0 dst src (.bool v) (by simpa [inner, LocalEnv.lookup_pushScope] using hd)
    (by simpa [inner, LocalEnv.lookup_pushScope] using hs) read write
  exact start.trans ((PickFreeRun.pure (sequence_next ctx _ [.returnStmt] inner k s)).trans
    (assignment.trans ((PickFreeRun.pure (sequence_next ctx .returnStmt [] inner k t)).trans
      ((PickFreeRun.pure (return_start ctx t inner (sequence [] inner k))).trans
        (.pure (return_sequence ctx t inner k []))))))

/-- The same invoke rule delivers a nonempty result after explicit return.
All memory premises reduce; only ordinary context lookup remains a premise. -/
theorem identity_call (ctx : ProgramCtx) (k : Continuation) (old v : Bool)
    (found : findFunctionIn? ctx.functions identity.id = some identity)
    (method : methodInfoByFuncId? ctx identity.id = none) :
    let s : Store := {heap := #[.value .bool (.bool old)]}
    let t : Store := {heap := #[.value .bool (.bool v), .value .bool (.bool v), .value .bool (.bool v)]}
    let env := LocalEnv.declare [] 7 (.base ⟨0⟩)
    PickFreeRun ctx ((SavedCaller.mk [7] env k).call identity.id [.boolLit v] s) (resumed k t) := by
  dsimp only
  let s : Store := {heap := #[.value .bool (.bool old)]}
  let a : Activation := ⟨(LocalEnv.declare [] 0 (.base ⟨1⟩)).declare 1 (.base ⟨2⟩),
    {heap := #[.value .bool (.bool old), .value .bool (.bool v), .value .bool (.bool false)]}, [.base ⟨2⟩]⟩
  let u : Store := {heap := #[.value .bool (.bool old), .value .bool (.bool v), .value .bool (.bool v)]}
  let caller : SavedCaller := ⟨[7], LocalEnv.declare [] 7 (.base ⟨0⟩), k⟩
  have activation : LocalEntry ctx identity [.bool v] s (.ok a) := .ready rfl rfl rfl
  have body := identity_body ctx a.store u a.locals (caller.boundary identity a).continuation
    (.base ⟨1⟩) (.base ⟨2⟩) v rfl rfl rfl (by cases v <;> rfl)
  exact caller.invoke .returned (.cons (fun tail => .pure (bool_literal ctx v caller.locals tail s)) .nil)
    found method rfl activation body rfl (.cons rfl .nil) rfl
    (.cons (by cases v <;> rfl) .nil)

#print axioms keep_set
#print axioms identity_body
#print axioms identity_call
end RD3SemanticClient
```

## Migration and remaining scope

Replace the downstream `callFrame` with `SavedCaller.boundary ...` and its
`.continuation`; replace `returnExit`/`bodyExit` with `exitPoint`/`NormalExit`.
Use `OperandValues`, `BoundDestinations` and `WriteValues` in new rule
statements. Their elementary inductive adapters above preserve the old
obligations. The pure part of the downstream `call_rule` can call
`SavedCaller.invoke` using the callee certificate's entry, body and readback
plus the ownership-derived destination writes. Drop its independent
`resultRoots` field: `LocalEntry.resultSlots` derives it. Result count still
relates destination arity to the callee signature/layout. This is semantic
arity, not target-plan validation.

Iris resources, KCallSpec and its ownership update protocol stay downstream.
The worker's files were not migrated in place. The checked scratch caller
examples show the new composition; downstream must migrate and recheck its
actual Iris callers at the returned immutable pin. Activation construction,
normalization and local binding facts still expose semantic memory operations.
Continuations and states remain transparent wrappers, so the whole API is
not representation-independent. Method dispatch, effectful operands, defers,
general refusal/outcome and observation coverage, and sequentialization
remain outside this batch. No evidence here retires the observer census.

## Validation

The targeted export/contracts/core-audit build passes (67 jobs). The frozen
acceptance package builds all twelve unchanged downstream files and both
harness modules (66 jobs); the six compatibility proofs, both original
acceptance wrappers and all three semantic-client theorems have only standard
axioms. Kernel replay passes for exactly 95 unique source modules: 81 GoLean
(including root `GoLean.lean`), twelve frozen downstream sources and the two
harness modules, with no missing, stale or duplicate module. The three built
Batteries dependencies (`CodeAction.Deprecated`, `Data.List.Basic`,
`Tactic.Alias`) also replay successfully; this is not a replay of the entire
Batteries library. Frozen hashes and byte identity of the reproduction proof
blocks against the built harness files were checked.

`LEAN_NUM_THREADS=2 capped scripts/ci --diff` passed in 741 seconds:
warning-free full build (194 jobs), core audit, 396 eval tests, frontend/Go,
wire/declaration/method/pin checks, exhaustive scheduler, 3,989 fresh
corpus rows (3,749 PASS, 240 classified known FAIL) and 405 negative rows.
Both baselines matched with no regression. One speedbump was red:
`check-mem-callsites` needed the new `WriteValues.storeLoc` premise inventoried
as a Prop-only mention. The inventory row was added with its no-execution
reason and the targeted checker rerun successfully (85 rows); every other
speedbump passed in the full run. The full run was on the pre-commit tree;
only documentation and this proof-only inventory row changed afterward.
No failure was waived and no semantic source changed after validation.

## Immutable handoff and audit dispositions

Implementation pin: `95f1eb64ca3bfa3c39fd5aa0792d516e76a31089`.
The fresh [independent audit](2026-10-14-rd3-independent-audit.md) found
no correctness defect or unmet obligation in this fragment. The reviewer
freshly elaborated changed modules and all acceptance inputs, replayed the
full GoLean prefix and acceptance closure, and added alias tests for both
normal exit modes. Before finalizing, it compared all 97 GoLean/Tests Lean
sources to the immutable commit and confirmed exact module-set and byte
equality. It also checked the final inventory correction and independently
reran that speedbump successfully. No prior audit verdict was supplied as
settled evidence. Full differential CI remains the implementer's validation,
not an independently rerun reviewer result.

[AGENT] 2026-10-14: retain the reviewed implementation. No finding needs a
fix or waiver; account for the six review conclusions and their limits:

| Review conclusion | Disposition |
| --- | --- |
| 1, exact compatibility | All six corrected propositions and both original examples checked without added assumptions. No change required. |
| 2, upstream-owned plumbing | Both semantic callers use `invoke`; Set's separate body proof is reused. Actual Iris caller migration remains downstream. |
| 3, result validity | Derived from activation, including duplicate identifiers; the original malformed-frame counterexample remains excluded. No semantic change or client root assumption. |
| 4, aliasing | Both exit modes checked with repeated roots, interior destinations and result/destination overlap. No distinctness restriction introduced. |
| 5, labels and fragment | Actual labels retained, every pick list empty; output silence is not asserted. Method dispatch, effectful operands and pending defers remain outside this fragment. |
| 6, remaining coupling | Activation/memory/binding/arity facts and transparent carriers remain visible. Iris ownership/protocol and broader observation/failure work stay open; do not claim complete adapter migration. |

Relay to logic: repin the experimental dependency to the implementation
commit above. Import `GoLean.Relational` and migrate the ordinary caller rule
to `SavedCaller.invoke` with upstream call/exit views. Use the six scratch
adapters only as exact compatibility evidence. The two unchanged examples
and both semantic callers pass; source laws have no missing-law parameters.
Recheck the actual Iris Keep/nonempty-result clients and their ownership
protocol at that pin. This response does not claim those downstream proofs
completed. The report-recording successor changes documentation only. No
merge, push or peer-tree mutation was performed.

## Subsequent downstream uptake

Logic has now consumed the implementation pin above: `4432ff2` implements
Keep and Identity through the shared Iris rule over `SavedCaller.invoke`,
and reviewed handoff `2941b01` accepts that experimental finite-caller
result. All six obligations are discharged and local call/exit plumbing
is removed. The migration instructions above describe the original handoff;
their RD3 uptake is complete. Existing guarded CodeX integration is the
next downstream target, with no new upstream semantic blocker demonstrated.
Full commit identities, provenance and RD4 readiness are recorded in the
[existing handoff](2026-10-14_relational-demo-laws.md#rd3-uptake-and-rd4-readiness).
