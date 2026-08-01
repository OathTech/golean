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

- 2026-08-01: **phase 2 landed — `go_walk`, and the summit re-derived
  through it.** The n = 1 `CommittedIndex` summit and the (non-quorum)
  recover composition are now walked by tactic, with
  `quorumOneKnownFuncSpec`'s statement and axiom set unchanged.

  **THE TACTIC.** `proofs/GoLeanProofs/Tactics/GoWalk.lean` (601 lines,
  ~230 of them the design note below). Four tactics: `go_walk` (the
  loop; `go_walk n` bounds it, `go_walk with [h]` extends the
  between-step normalization), `go_walk_step law as […] with […]` (one
  law given as a TERM with its semantic side conditions supplied — the
  replacement for a hand walk's `iapply (…) / isplitl [H] / iexact H /
  iintro H` block), `go_walk_finish H` (walk until the goal is the one
  the continuation hypothesis `H` delivers, then close it), and
  `go_walk1` (one step, reporting which law fired — debugging only).

  **ARCHITECTURE DECISION: (a), attribute-registered law table.** The
  arc plan offered (a) attribute registration + goal matching, (b) a
  hand-written match on `Config` constructors, (c) aesop/simp-style rule
  sets. **(a) is chosen and (b) is explicitly rejected** — a `match` on
  `Config` would put the law table INSIDE the tactic, so every new law
  family would edit the tactic and the tactic would grow a dependency on
  GoCore. As built, `@[go_walk_law]` on a theorem whose type ends in
  `… ⊢ WP c @ s ; E {{ Φ }}` inserts `c` into a `DiscrTree` keyed by the
  law's own conclusion, and `Tactics/GoWalk.lean` imports **only `Lean`,
  `Iris.ProofMode` and `Iris.ProgramLogic.WeakestPre`**: it cannot name
  GoCore, let alone quorum, because it cannot see them. (c) was rejected
  because our step laws are ENTAILMENTS between `iProp`s with resource
  premises, not rewrite rules; simp/aesop would have to be taught the
  proof mode from scratch.

  Three mechanisms are ours rather than inherited, each forced:
  1. **Most-specific-first candidate order.** `DiscrTree.getMatch`
     returns wildcard branches BEFORE literal ones, which is exactly
     backwards here: a law like `wp_stmt_op_first`, whose conclusion is
     `Config.exec stmt env k` with `stmt` a variable, matches every
     statement and would fire in front of the composed operation law
     that covers the statement whole. Entries carry a specificity (their
     count of non-wildcard keys) and candidates are sorted by it.
  2. **The boundary rule.** If a law matched the configuration and its
     side conditions were mechanical but its resource premises could not
     be framed against the Iris context, the walk STOPS there instead of
     falling through to a more generic law. That is the honest reading —
     the composed law covers this statement, the generic one would
     descend into it — and it is what makes `go_walk; go_walk_step
     (wp_map_lookup_ackedIndex …)` work without counting steps.
  3. **Per-candidate heartbeat budgets.** A law that does not apply can
     be arbitrarily expensive to reject (`isDefEq` on two large
     configurations, `rfl` unfolding the interpreter). Match and side
     conditions each run under their own small budget, so the failure is
     "this law did not fire", not a timeout reported at a tactic that was
     going to succeed.

  **BOUNDARIES HONOURED (where it stops, by design).** No registered law
  matches the configuration (reported with the configuration's head
  shape); a side condition that is a real semantic obligation
  (`wp_assign_store`'s `hstore`, `wp_init`'s `hdef`, the `applyStrictOp`
  blobs) rather than `rfl`/`assumption`/normalization; invariant-carrying
  rules (`wp_map_iter_inv` is deliberately NOT registered — its `I` is
  human-supplied, and `wp_ci_loop_one` still writes the invariant and its
  entry/exit split by hand, unchanged); a resource it cannot frame. It
  never loops (explicit fuel), never `sorry`s, and every failed candidate
  is fully backtracked.

  **RESOURCE THREADING — v1 policy, as landed.** The COMMON case is
  automatic: `iframe` cancels the law's resource premises against the
  context and the continuation's wand is re-introduced. The cost, found
  by building it: **framing renames**. A hypothesis `iframe` consumes
  comes back inaccessible, so a walked proof cannot address its resources
  by name afterwards. Two consequences, both now in the code: segment
  endings are `go_walk_finish H` / `iframe` (name-free) instead of
  `isplitl [H₁ … Hₙ]`, and `go_walk_step … as [x, H, …]` exists for the
  few cells a later obligation genuinely must name (the range invariant's
  `i` cell in `wp_ci_loop_one`, the `$c3`/`r` target cells at the two
  callsites). This is the arc plan's "fallback" outcome reached from the
  ambitious side: automatic where unambiguous, explicit where the human
  needs a name.

  **NORMALIZATION.** `simp only [go_walk_simp]` runs between steps. The
  Lean-core half (`List` append/length/reverse normal forms, `reduceIte`,
  `String.reduceBEq`, `Option.isSome_none`/`toList`) is tagged in
  `Laws/Control.lean` beside `seqCont_splice`, which is HOISTED there
  from the two spec files that each restated it. Two simprocs were needed
  and are the only new semantic content: `reduceIntKindNormalize`
  (`Laws/Eval.lean`) evaluates `IntKind.normalize` at a literal and puts
  the answer back in `OfNat` form — the hand walks wrote
  `rw [show IntKind.int.normalize 0 = 0 from by decide]` twelve times;
  and `reduceGroundDecide` (`Laws/Control.lean`) reduces a ground
  `decide p`, because `wp_strict_apply_pure` now COMPUTES a comparison's
  answer instead of being told it (`(out := .bool true)` was the hand
  walks' guess). At a non-literal the walk carries the normalization as a
  hypothesis instead: `go_walk with [hq]`.

  **ACCEPTANCE (the phase-0 checkable facts).**
  - *Statement identity*: `summitStatement_pinned` /
    `summitStatement_holds` in `Specs/AutomationTargets.lean` compile
    unchanged — the re-derivation inhabits exactly
    `quorumOneKnownFuncSpec_statement`. Not one theorem STATEMENT in
    `Specs/GoldenQuorumWP.lean` changed; only the tactic scripts did.
  - *Axiom identity*: the `#guard_msgs in #print axioms
    GoLean.Surface.quorumOneKnownFuncSpec` pin in `Audit.lean` still
    reads `[propext, Classical.choice, Quot.sound]`, and the whole-module
    sweep is green at **6227 declarations, all axiom-clean** (was 6126;
    the growth is the tactic's own definitions).
  - *Coverage identity*: `wp_committedIndex_body` and every body lemma it
    composes are still the things being proven; the
    `example := @…wp_committedIndex_body` reference compiles.

  **RETIREMENTS.** The superseded content is the hand-walk TACTIC TEXT,
  not any lemma: all 15 walks in `Specs/GoldenQuorumWP.lean` and
  `wp_recoverDirect_body` in `Specs/GoldenRecover.lean` were rewritten in
  place, so every name, statement and downstream use survives and nothing
  is orphaned. The one deletion is the two local restatements of
  `seqCont_splice` (`GoldenQuorumWP`, `GoldenSliceWP`), replaced by the
  single `GoLean.Iris.seqCont_splice` in `Laws/Control.lean`;
  `GoldenRecover`'s `open … (seqCont_splice)` went with it.

  **LINE COUNTS (evidence, not the criterion).**
  `Specs/GoldenQuorumWP.lean` 2914 → 1429 (−51%);
  `Specs/GoldenRecover.lean` 426 → 201 (−53%). Counting only the tactic
  scripts of the 15 quorum walks: **1891 → 506 lines (−73%)**. The
  largest single walk, `wp_ci_range_body_one`, went 329 → 62; the driver
  body `wp_oneKnown_body` 391 → 118; `wp_ci_emptyIf` 46 → 3
  (`go_walk; go_walk_finish Hcont`). Against that, +601 lines of tactic
  and +130 of law-module registration/normalization — machinery that is
  paid once and amortized over every future walk. NOTE the arc plan's
  "≤ ~100 lines" acceptance is NOT met at the summit taken as a whole
  (506), and should not be: what did not shrink is exactly the semantic
  content — the `storeLoc`/`applyStmtOp`/`defaultValue` witnesses and the
  frame-entry pins — which is proof obligation, not walking.

  **GENERALITY DEMONSTRATION (non-quorum).**
  `wp_recoverDirect_body` (`Specs/GoldenRecover.lean`) — the recover
  composition over the pinned lowering: defer registration, `panic`, the
  panic-path drain of the lambda-lifted closure, `recover()`, the guarded
  write through the captured pointer, the recovered marker cancelling the
  unwind. Re-derived at 277 → 52 tactic lines with the SAME tactic and no
  new mechanism; the only additions were `@[go_walk_law]` on three unwind
  laws (`wp_defer_register_noargs`, `wp_panic_unwind`, `wp_recover`) and
  `List.reverse_cons`/`reverse_nil` in the normalization set. That the
  panic/defer/recover family registered without touching the tactic is
  the evidence the table is general.

  **OVER-SPECIALIZATION CHECK (standing item).** The tactic core imports
  `Lean`, `Iris.ProofMode`, `Iris.ProgramLogic.WeakestPre` and NOTHING
  else — no GoCore, so no `Config` constructor, no statement form, no
  program name occurs in it; `grep -E 'quorum|GoCore|Config\.' ` matches
  only prose in the module docstring. Law registration is at each law's
  own definition site. The QUORUM-specific composites that are registered
  (`wp_map_lookup_ackedIndex`, the two `AckedIndex` frame entries) are
  entries in a table, not tactic code, and were registered because a walk
  needed to STOP at them; the three witness lemmas that were briefly
  tagged (`wp_sort_slice_srt`, `wp_make_slice_c2`,
  `wp_map_range_snapshot_committed`) were untagged again — a witness is
  not a law.

  **Gate**: `scripts/ci` PASS — escape-hatch preflight, proofs-file audit
  coverage, golden lowering, surface purity, warning-free core build,
  proofs + in-build `Audit` gate (6227 declarations, axiom-clean), 44/44
  eval tests, negative baseline 309/309 and differential baseline 873/873
  with no drift. No runtime code was touched (proofs only), so no
  baseline re-pin and no `--diff` re-run is owed.

  **What phase 3 needs to know.** (i) A walk that must stop in front of a
  segment the human takes whole needs `go_walk n` with a small explicit
  `n`, because `wp_stmt_op_first`'s conclusion matches every
  `Config.exec`; three such sites exist in the summit and each is
  commented. Making that unnecessary means either splitting
  `wp_stmt_op_first` per `StmtOp` or teaching the walk a "stop before an
  opaque pin projection" rule — worth doing before the 3-voter rung
  multiplies the sites. (ii) `go_walk_step`'s law term is elaborated
  AGAINST the goal's weakest precondition, so its `by simp …` side
  conditions see real goals; that path silently falls back to an
  unconstrained elaboration if the law is given with explicit arguments
  still open. (iii) Nothing in the tactic knows about `k`-ary anything —
  the 3-voter rung's cost is the invariant and the resource split, both
  already human territory.
