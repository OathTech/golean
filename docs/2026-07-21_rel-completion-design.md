# Arc C: Rel completion — D2-proper, D1 splice, D3 panic rules

Date: 2026-07-21. Branch `rel-completion`. Design of record for the three
trusted-relation edits discovered by Arc B's correspondence work (origin:
`docs/2026-07-21_eval-totalization-correspondence.md`). One arc, three
semantic commits (one concern each), one downstream re-proof wave per commit,
three-auditor pre-merge bar. Runtime (`Eval`) untouched by construction —
`Rel.lean` is proof-facing; the differential cannot move (ci still runs).

**Execution order: D2 → D1 → D3.** D2 deletes the returning-env and with it
the whole `avoid`/`TopAvoid`/agreement machinery in the correspondence; doing
it first means D1's new splice cases are built on the smaller machinery, not
on code about to be deleted.

## D2-proper: result locations in `Cont.frame` (frame exit reads state, not env)

**Today**: `frameReturn` reads named results by looking ids up in the
`returning`-carried env (the env *at the return point*, inner scopes
included); the interpreter reads them after block scopes pop. Divergent under
block-scoped shadowing — held off only by the correspondence's
`avoid`-discipline. `frameFall` reads nothing (fall-through results gap).

**Design**: resolve result **locations** at call time, when they are
unambiguous — immediately after `DeclsR` allocates them in the fresh frame:

- `Cont.frame (targets : List Loc) (results : List Loc) (k : Cont)` —
  locations, not `Param`s.
- `Step.call` gains a premise resolving each result id in `frameEnv` to its
  location (`LookupsR frameEnv func.results resultLocs` — deterministic; the
  ids were just declared by `DeclsR`).
- `frameReturn` reads the **state** at those locations (`LoadsR s resultLocs
  vs`) and stores to targets. The returning env is no longer consulted.
- **`Config.returning` drops its env entirely** (`.returning (k : Cont)`),
  restoring the symmetry with the other unwinding configs. `wp_return`,
  `seqReturn`, `loopReturn` simplify.
- `frameFall` now ALSO reads the result locations and stores — erasing the
  fall-through results gap: fall-through of a value-returning function stores
  the declared defaults, which is **exactly what the interpreter does**
  (`readResultList` on the normal outcome). Go forbids that shape statically,
  but where the relation must say something, it now says the same thing as
  the interpreter instead of something different.

**Payoff in the correspondence** (why this pays for its re-proof wave):
`Eret`/agreement/`TopAvoid`/`avoid`-index all become unnecessary — T1/T2's
returned cases collapse to the same shape as broke/continued; `SpineFrag.init`
drops its `∉ avoid` side-condition; `FuncFrag` drops the avoid plumbing AND
the `EndsRet` requirement (fall-through now correct for all arities).

**Re-proof wave**: `Laws/Control` (`wp_return`, `wp_seq_return`,
`wp_frame_fall`), `Laws/Call` (`wp_call_*`, `wp_frame_return*`), `Specs`
(`wp_inc_call`, `wp_main_call`, `slice_adequate` composition), `Inversions`
as needed, T1/T2 returned machinery (net deletion), witness.

## D1: seqn splice — one total rule via `seqCont`

**Today**: `Step.seqn` wraps every executed `.seqn` in its own `Cont.seq`,
whose env is discarded at `seqDone` — so a frontend-lowered declaration
(`x := 1` → nested `.seqn #[init x, assign x 1]` spliced into the enclosing
block list) dies at the end of its desugaring seqn. The relation cannot run
any frontend-lowered program with a declaration.

**Design**: replace the wrap rule with ONE total, deterministic rule whose
continuation is computed:

```
def seqCont (ss : List Stmt) (env : LocalEnv) : Cont → Cont
  | .seq rest env' k => if env' = env then .seq (ss ++ rest) env k
                        else .seq ss env (.seq rest env' k)
  | k => .seq ss env k

| seqn {ss env k s} :
    Step (.exec (.seqn ss) env k) s (.next (seqCont ss.toList env k)) s
```

Rationale: when a nested seqn is entered *from* a governing seq (`seqNext`),
the two envs are equal by construction — that reachable case splices, so
mid-seqn declarations extend the env of the *enclosing* rest, matching the
interpreter's scope-transparent `.seqn` (and Go: statement lists splice, only
blocks scope). The env-mismatch fallback wraps (unreachable from real
programs; kept for totality/determinism rather than a stuck hole — a
deliberate exception to fail-closed, recorded here: wrapping is the current
behavior, so the fallback is at worst the old semantics, never a new claim).
Determinism is by construction (one rule, function conclusion) — the WP layer
keeps `wp_lift_pure_det_step_no_fork`.

**Correspondence extension**: `SpineFrag` gains
`| seqnSpine : (∀ s ∈ ss, SpineFrag avoid s) → SpineFrag (.seqn ss)` — a
nested seqn in spine position is now legal WITH declarations, and T2's head
case for it uses the splice rule (the interpreter side is already
scope-transparent). `StmtFragNS.seqn` (NS-only elements, non-spine
positions) remains.

**Re-proof wave**: `wp_seqn` (conclusion now `seqCont …`; concrete-cont uses
reduce by `simp [seqCont]` — `.stop`/`.frame` callers unchanged after simp),
its witnesses, T1 seqn case, T2.

## D3: panic propagation completeness in `ExprR` + the call legs

**Today**: operand panics propagate only through `add/sub/mul/div`
(`binPanicLeft/Right`). A panic inside `eqCmp`/`deref`/`fieldGet`/`indexGet`
operands, or inside a call's target/argument legs, has no derivation — the
relation is stuck where the interpreter (and Go) panics. Fail-safe for
adequacy (unprovable, not unsound) but incomplete, and it blocks the panic
side of the correspondence.

**Design** (additive rules):
- `ExprR`: `eqPanicLeft/Right`, `derefPanic` (operand-expr panic; `derefNil`
  already covers the nil case), `fieldGetPanic`, `indexPanicBase/Index`
  (operand-expr panics; `indexGetPanic` already covers the bounds case).
- Call legs: panic-outcome variants for the resolution relations
  (`AssigneesR`/`ArgsR` gain panic constructors or a parallel `…Panic`
  judgment) + `Step.callTargetsPanic` / `Step.callArgsPanic` ending in
  `.panicked`.
- Then **`interpreterPanic_frag`**: the panic-side mutual induction (T1p/T2p
  mirroring T1/T2), converting `interpreterPanicStatement`'s fragment
  restriction into a theorem. If the induction turns out heavier than
  budgeted, it may split into its own follow-on commit series *within the
  arc* — but the arc does not merge without it; the semantics rules without
  the correspondence would be exactly the untested-law shape our gates exist
  to prevent.

**Re-proof wave**: `Inversions` determinism lemmas gain refutation cases
(operand value/panic exclusivity, from operand determinism); WP laws that
invert `ExprR` re-elaborate.

## Goose/Perennial cross-check (per the mapping mandate — adopt or reject, not rediscover)

Checked against `../deps/perennial/new/golang/defn/{exception,loop,postlang}.v`
and `../deps/goose/glang` (new Goose, 2026-07-21):

- **D2** — new Goose's exception encoding (`do:`/`return:` tagged pairs,
  `;;;` short-circuit, `exception_do` unwrap) carries the return **value in
  the control signal**; named results are rewritten by their translation so
  the frame exit never reads result cells. Our IR's returns are bare (values
  land in result cells via explicit `assign $res0` before `return`), so the
  faithful CEK adaptation is locations-pinned-at-call-time — **adopted as
  adapted**. Their uniform function-boundary unwrap (fall-through legal,
  no separate path) validates the `frameFall` unification. Their `do_for`
  tag-dispatch is the shallow twin of our `loopNext/Continue/Break/Return`
  rules — structural corroboration, nothing to change.
- **D1** — Goose has no statement lists: declarations become `let:` binders,
  so splice-scoping is done by the *translation*. We keep Go-shaped statement
  lists deliberately (differential fidelity of the IR); `seqCont` is the
  CEK-side equivalent of their let-flattening. **Lesson adopted, mechanism
  necessarily different.**
- **D3** — GooseLang `Panic` is a stuck expression: panics are unsafety, never
  behavior; proofs imply panic-freedom. **Deliberate divergence retained**:
  our differential oracle observes real Go panics (messages compared), so
  `.panicked` is explicit behavior. Verified programs end up panic-free under
  both designs; ours additionally lets the semantics *model* panicking
  programs, which the oracle requires. No Goose analogue to copy for the
  D3 completeness rules.

## Validation per commit

`scripts/ci` (runtime untouched ⇒ baseline diff rides on the last full run;
any Eval edit would be a scope violation for this arc). Audit gate: every new
rule's docstring claims only what its correspondence case demonstrates;
`interpreterPanic_frag` is D3's non-vacuity witness; D1's is the T2
splice-case + (Arc D) the golden-lowering slice; D2's is the simplified
frameReturn correspondence + the retirement of the avoid machinery.


## Completion record (2026-07-21, end of arc work)

All three landed as designed, four commits: D2-proper (f5a1557, net
deletion), D1 (24a3d3e, splice + strip-target machinery + tail-generalized
T2 + `seqnSpine`, witnessed on the frontend shape), D3a (2521e61, panic
rules + call-leg judgments + expression/assignee panic bridges; discovered
and fixed a FIFTH divergence — `divByZero` demanded an int left operand
while the interpreter checks the divisor first), D3b (T1p/T2p statement
panic induction + substrate panic-freedom lemmas + `interpreterPanic_frag`
+ `interpreterPanic_spineSeq`, witnessed on `x := 1; x = 1/0`). Both of
item 6's Props now have fragment-scoped THEOREMS: `interpreterSound_frag`
and `interpreterPanic_frag`. The unrestricted Props' remaining falseness is
solely the richer-interpreter scope (the D1 counterexample is gone).
