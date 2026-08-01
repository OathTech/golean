# Arc: proof automation (2026-08-01) — make general theorems cheap, then take them

Decided with the user 2026-08-01, immediately after the quorum-pilot
merge (`main` @ bfe5496→ae1b9ee; corpus 872/602, Audit sweep 6036,
the n=1 summit proven). Chosen over a pure coverage-broadening arc
because PROOF COST is now the binding constraint: the n=1
`CommittedIndex` walk cost ~2,800 hand-written tactic lines, and every
future theorem — 3-voter, `VoteResult`, joint configs, the raft safety
stack — pays that toll again until the walking is automated.

## THE GOAL

**The ∀-config `CommittedIndex` theorem, proven by automation**: for
EVERY config and acked map (machine-side generality matching
`committedIndexRef_meets_spec`'s math-side generality), the real
etcd-io/raft `CommittedIndex` over the pinned lowering satisfies
`IsCommittedIndex` — with the proof produced by a walk tactic and an
inductive range rule, not by hand-enumerated steps.

## The two machinery pieces

1. **`go_walk` — the walk tactic.** The summit proof is mechanical:
   inspect the WP goal's configuration, select the one law whose
   conclusion matches (the law tables are finite and shape-indexed),
   apply it, discharge the standard modality dance
   (`fupd_intro`/`inext`/credit intro) and the rfl/simp side
   conditions, repeat until the goal is the continuation the human
   cares about (a resource split, a nondet branch, an invariant).
   Human-written proof shrinks to: entry resources, the invariants at
   choice points, and the final entailment. ACCEPTANCE: the existing
   n=1 summit re-proves in ≤ ~100 lines with identical statement and
   axiom set.
2. **The inductive range rule.** `wp_map_iter_next_key` already
   quantifies over ALL (index, address) choices — compose it with a
   loop-invariant-style rule over the remaining snapshot (an
   `I : Array (GoValue × GoValue) → iProp` preserved by one arbitrary
   iteration ⟹ WP of the whole range), so k-voter proofs are
   ONE generic-iteration obligation + an invariant, independent of k!
   orderings. This is the nondeterministic analogue of `wp_while_inv`
   and the piece that makes ∀-config reachable at all.

## Phases (statement-first throughout)

0. **Targets.** `def … : Prop` statements: the ∀-config theorem (over
   the pinned lowering, config/acked data supplied through the driver
   env/heap — the statement design must handle "for all heaps encoding
   a config" honestly, likely via an encoding predicate); the 3-voter
   concrete instance; the range-invariant rule's intended statement;
   negative twins. Plus the automation acceptance criteria as
   checkable facts (line counts are advisory; the REAL acceptance is
   "statement and axiom set identical to the hand proof").
1. **The inductive range rule**, proven and witnessed (a non-quorum
   witness FIRST — e.g. a sum-over-map program — per the
   over-specialization standing check; then the quorum instance).
2. **`go_walk` v1**: deterministic spine only (the law classes the
   summit walk used); acceptance = summit re-derivation. Design note
   on the tactic architecture (syntactic goal-matching vs typeclass
   resolution vs macro table — record the choice and the Perennial/
   Goose comparison: their `wp_` tactic families in
   `deps/perennial/src/program_logic` and proofgen are the prior art).
3. **Compose**: 3-voter theorem via rule + tactic; then ∀-config.
   Spec-surface widenings (n-ary entry/exit, key+value range) land
   where forced, witnesses same-commit.
4. **Rider (folded in where the automation's test programs need
   them, else own slices at the end):** method promotion (BUG-007),
   BUG-005 snapshot fix, import-path identity (BUG-010 widening),
   type switches. Each is coverage work in the established
   guardrails-first pattern.

## STANDING CHECK: over-specialization

Carried over verbatim from the quorum-pilot arc
(`docs/2026-07-30_quorum-pilot-arc.md` §STANDING CHECK) — it is a
permanent audit dimension now. Specific to this arc: the TACTIC must
be general over the law tables (a new law family registers; the tactic
does not hardcode quorum shapes), and the range-invariant rule's first
witness must be a non-quorum program.

## Out of scope

Concurrency (BUG-002 unchanged), floats/generics/channels, the fuzzer
side project (own loop, `side/gofuzz/`), frontend work beyond the
rider items.

## Exit criteria

- Phase-0 statements proven (∀-config + 3-voter + rule); summit
  re-derived through `go_walk` with identical statement + axioms;
  every new law/rule witnessed same-commit; sweep clean; gate green;
  ratchet not up.
- Pre-merge audit ask (unconditional; over-specialization dimension
  included) + merge sign-off.

## Build log

- 2026-08-01: arc opened on `proof-automation`; this plan of record.
- 2026-08-01: **phases 0 + 1 landed in one slice** — the phase-0 target
  statements and THE INDUCTIVE RANGE RULE, proven and doubly witnessed.

  **The rule.** `GoLean.Iris.wp_map_iter_inv`
  (`proofs/GoLeanProofs/Laws/Range.lean`): for an invariant
  `I : Array (GoValue × GoValue) → IProp` over the REMAINING snapshot,
  one generic-iteration obligation (arbitrary `rem`, arbitrary pick `i`,
  arbitrary allocated key address `pa`) plus `I entries` and
  `I #[] -∗ WP (Config.next k)` entails the WP of the whole range.
  Proven by ordinary **Nat induction on `remaining.size`** — the snapshot
  strictly shrinks at every `mapIterNext`, so unlike `wp_while_inv` no
  Löb is needed; the `▷` is spent inside `wp_map_iter_next_key`'s own
  lifting. Composes `wp_map_iter_next_key` at each step and
  `wp_map_iter_done` at `#[]`.

  **Deltas from the sketch in phase 1 of this plan, each forced by the
  proof:**
  1. The body obligation ENDS AT `Config.next` of the SHRUNK `mapIterK`,
     not at a `{{ _, I (rem.eraseIdx i h) }}` postcondition. The WP's
     postcondition is fixed (`Φ` for the whole configuration), so the
     "rest of the loop" has to arrive as a WAND, exactly as
     `wp_while_inv`'s `Hbody` does. Shape:
     `I rem ∗ pa.id ↦ keyCell ∗ (I (rem.eraseIdx i h) -∗ WP (next (mapIterK … shrunk …))) ⊢ WP (exec body (env.pushScope.declare kid pa) (mapIterK … shrunk …))`.
  2. `hnorm` is MEMBERSHIP-indexed (`∀ p ∈ entries`) where
     `wp_map_iter_next_key`'s is INDEX-indexed. The induction needs to
     push the premise through `eraseIdx`, which is one line at
     membership (`Array.mem_of_mem_eraseIdx`) and awkward at indices.
     The `σ.types` ghost pin rides along unchanged.
  3. The key cell is the BODY'S, affinely: it is handed to `Hbody` fresh
     each iteration and never asked back, so `I` never mentions it. That
     is the honest model — `bindIterVars` allocates a new cell per
     iteration and nothing frees it — and it is what keeps `I` a function
     of the snapshot alone.
  4. `Hbody` quantifies over EVERY array, not only reachable ones. No
     reachability relation is needed because `I rem` is an ANTECEDENT
     there: an invariant carrying its own reachability fact discharges
     the unreachable instances from a false hypothesis. Both witnesses
     use this (the quorum one literally: `I rem` names the two reachable
     snapshots).
  5. **`break`/`continue` are OUT of v1**, recorded as a completeness
     scope, not a soundness side-condition: the rule is sound for any
     body, but a body that breaks or continues has no route through the
     single (normal) exit wand it is given. `continue` is the cheap
     widening (its target IS the normal one — one pure-step law);
     `break` needs a second, break-time exit wand `∀ rem, I rem -∗ WP
     (Config.next k)`. Neither is needed by the walks in flight.

  **Witnesses (the arc's non-quorum-first requirement).**
  1. `wp_map_iter_inv_key_sum_witness` — `for k := range m { sum = sum + k }`
     over an ARBITRARY snapshot of nonnegative `int` keys whose total
     fits in an `int`, invariant "`sum` holds the total of the entries
     consumed so far", conclusion holding for all `entries.size!`
     iteration orders. Guardrail added first, per guardrails-before-tool:
     corpus case `range/range-map-key-sum` (differential PASS; the
     baseline is re-pinned in this commit for exactly that one row). The
     witness's body term is HAND-BUILT and its docstring says so — it is
     evidence the premises are jointly satisfiable by a real program
     shape, not a claim about a lowering.
  2. The QUORUM instance is a REWIRING, not a new theorem:
     `wp_ci_loop_one` (the n = 1 summit's voter loop) now discharges its
     range segment THROUGH the rule. The body walk was extracted verbatim
     as `wp_ci_range_body_one` (only the three `"i"` lookups changed, to
     resolve through a hypothesis now that the environment is a
     variable), and the invariant names the reachable snapshots
     (`#[voter 1]` before, `#[]` after) with the resources the body
     actually touches; `n`, `c` and the config data cell stay ambient.
     **`quorumOneKnownFuncSpec`'s statement and axiom set are unchanged**
     — which is precisely the acceptance shape phase 2 needs.

  **Phase-0 targets** (`proofs/GoLeanProofs/Specs/AutomationTargets.lean`,
  `def … : Prop`, unproven by design):
  - `committedIndexAllConfigs_statement` — THE GOAL. **Design decision
    (a) over (b)**: quantify over INPUTS by encoding them in the HEAP and
    stating `GoSpec` at the real method
    `main.MajorityConfig.CommittedIndex`, with `EncodesConfig` /
    `EncodesAcked` relating the map SNAPSHOT ARRAYS to `(c, acked)` —
    rather than (b) a parameterized driver family. Reason: under (b) the
    theorem's subject would be programs we generate, so the generality
    would live in our generator rather than in the claim about the
    vendored etcd-io/raft method; that is the over-specialization failure
    mode the standing check names. The encoding is stated on the snapshot
    arrays (pure data), NOT as a `Heap → … → Prop`, because `GoSpec`'s
    `InitialSplit` already quantifies over every heap containing the
    footprint. Nothing bounds `c.length`, so the target covers BOTH sides
    of `if len(stk) >= n`. Cost recorded as OWED: `GoFuncSpec` has no
    caller-environment parameter, so a heap-carried receiver is not
    denotable through it (the defect `GoFuncSpec2` was widened to fix);
    the target is therefore written as the `GoSpec` it unfolds to, and
    the unary-with-`argEnv` widening is owed at discharge time.
  - `quorumThreeAllFuncSpec_statement` (3-voter concrete rung, `= 6`) and
    its negative twin `quorumThreeAllNotTwelve_statement`, carrying the
    same honesty note as `quorumOneKnownNotEleven_statement` (an
    unconditional refutation needs a terminating run EXHIBITED; it is a
    target, not a corollary).
  - `mapIterInvRule_statement` — the rule's intended statement as its own
    target, discharged in the same commit by `mapIterInvRule`.
    **Provenance is stated in the file**: this is a same-commit target,
    not a written-first one (the pilot's audit finding 6 exists because
    that was fudged once).
  - Non-vacuity of the targets themselves: `encodesConfig_three` exhibits
    an encoding; `committedIndexRef_threeAll` (`rfl`) computes the value
    the 3-voter rung must produce and `isCommittedIndex_threeAll` upgrades
    it, with two negative twins; and `committedIndex_arity_in_pin` /
    `committedIndex_types_in_pin` pin by `rfl` the signature facts whose
    violation made the FIRST `GoFuncSpec2` statement FALSE rather than
    merely unproven.
  - **Phase-2 acceptance as checkable facts**, not prose:
    `summitStatement_pinned` / `summitStatement_holds` (statement
    identity — the `go_walk` re-derivation must inhabit the same type),
    the `#guard_msgs in #print axioms` gate on `quorumOneKnownFuncSpec`
    in `Audit.lean` (axiom identity), and an `example` reference to
    `wp_committedIndex_body` (coverage identity: the tactic replaces the
    WALK, not the claim). Deliberately NO line-count assertion — a budget
    is not a correctness property.

  **Over-specialization check, per new law (standing item).**
  `wp_map_iter_inv` — TARGET-FREE: key variable, key/value types, body,
  snapshot, environment, continuation and invariant are all law
  variables; no quorum name, value or program fragment occurs in the
  statement. Narrowings recorded above (key-only, normal-completion-only)
  are language-capability scopes with widening paths, and the FIRST
  witness is non-quorum by construction. Supporting lemmas
  (`keyIntSum_eraseIdx`, `keyIntSum_nonneg`,
  `int_normalize_of_nonneg_lt`) are about arrays and `IntKind`, not about
  any program.

  **Goose/Perennial comparison** (verbatim citation, in the law's
  docstring too): the prior art is `wp_map_for_range`
  (`deps/perennial/new/golang/theory/map.v:213`, with
  `wp_InternalMapForRange` at :24 and the `wp_for` family in
  `theory/loop.v:71`). Theirs owns the map (`mref ↦{dq} m`), quantifies
  ONCE over an arbitrary key ORDER (`∀ keys`, `NoDup`, `list_to_set keys
  = dom m`) and indexes the invariant by that order and a POSITION
  (`P keys i`), with a `□`-boxed step obligation. Four deltas: (i) our
  nondeterminism is quantified PER STEP rather than up front, so our
  conclusion covers interleavings a commit-to-a-list-first model cannot
  state — the "we cover more" direction the standing check allows;
  (ii) `I remaining` vs `P keys i` is the same information without a
  ghost order to maintain; (iii) their `□` is our Lean-level `∀`, free;
  (iv) they handle `break`/`continue`/`return` via
  `for_map_postcondition` (`map.v:207`) and the exception monad, we do
  not — a REAL narrowing, recorded with its widening path. Separately,
  they read the LIVE map while we consume the machine's snapshot: that is
  BUG-005, a semantics gap already cross-referenced in `Laws/Range.lean`,
  not a proof-rule gap.

  **Gate**: `scripts/ci` green; proofs build + in-build `Audit` sweep
  (6126 declarations, all axiom-clean, new `#guard_msgs` pins on
  `wp_map_iter_inv` and its witness); full native differential re-run —
  873 cases, 603 pass, drift vs the previous baseline EXACTLY the one new
  guardrail id, so the baseline is re-pinned in this commit with that
  reason.

  **What phase 2 needs to know.** The summit walk is now
  `wp_ci_loop_one` → `wp_map_iter_inv` → `wp_ci_range_body_one`, so
  `go_walk` must handle a goal whose next law is chosen by a Lean-level
  premise (a rule application with `(I := …)`), not only by the WP goal's
  configuration — i.e. the tactic's law table has to stop at
  invariant-carrying rules and hand back to the human, exactly as at
  resource splits and nondet branches. Everything below that boundary
  (the ~330-line body walk, and the pre/post segments of
  `wp_ci_loop_one`) is the pure deterministic spine `go_walk` v1 targets.
