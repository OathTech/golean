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

**Status 2026-08-01 (close-out): MET**, except the rider items, which
are deliberately deferred (subsection below):

- ~~Phase-0 statements proven (∀-config + 3-voter + rule)~~ **MET**:
  `committedIndexAllConfigs` (phase 4), `quorumThreeAllFuncSpec`
  (phase 3), `mapIterInvRule` (phase 1) each discharge their phase-0
  `def … : Prop` target with the `theorem … : <the def>` statement-
  identity check.
- ~~Summit re-derived through `go_walk` with identical statement +
  axioms~~ **MET** (phase 2): `summitStatement_holds` still inhabits
  `summitStatement_pinned`, and the `#guard_msgs` axiom pin on
  `quorumOneKnownFuncSpec` still reads the classical trio.
- ~~Every new law/rule witnessed same-commit; sweep clean; gate green;
  ratchet not up~~ **MET**: per-phase gate records in the build log;
  close-out `scripts/ci` PASS (sweep 6636 declarations axiom-clean,
  differential 873/873, negative 309/309, no drift, no re-pin).
- Pre-merge audit ask (unconditional; over-specialization dimension
  included) + merge sign-off — **the remaining step**; both new
  doctrines (`docs/2026-08-01_tcb-and-layering-doctrine.md`) are named
  audit dimensions for it.

### Deferred to future arcs (coordinator decision 2026-08-01)

The plan's phase-4 RIDER items are moved out of this arc's merge scope —
**not started, not blocked, deliberately excluded**; each is coverage
work in the established guardrails-first pattern, independent of the
∀-config theorem this arc existed to prove:

- Method promotion (BUG-007).
- BUG-005 snapshot fix (range reads the live map in Go, the snapshot in
  GoCore — cross-referenced in `Laws/Range.lean`).
- Import-path identity (BUG-010 widening).
- Type switches.

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

- 2026-08-01: **phase 3, part 1 — THE 3-VOTER THEOREM, and the n-voter
  loop law.** `quorumThreeAllFuncSpec` discharges the phase-0 target
  `quorumThreeAllFuncSpec_statement`: etcd's own `majority_commit.txt`
  row — `committedThreeAll()` over `MajorityConfig{1,2,3}` with
  `mapAckIndexer{1:12, 2:5, 3:6}` — returns `6` over the PINNED lowering,
  at `GoFuncSpec` strength, with the declarative restatement
  `quorumThreeAllMeetsSpec` (`IsCommittedIndex [1,2,3] ackedThreeAll`),
  the first-order readout `quorumThreeAllReturnsSix` and the
  run-conditioned negative twin `quorumThreeAllNotTwelve` (at `12`, the
  largest acked index). New file: `Specs/GoldenQuorumThree.lean` (1457
  lines) plus `Laws/Values.lean` (245).

  **THE POINT OF THE EXERCISE, MET: no iteration order is enumerated
  anywhere.** At n = 3 the map range has `3! = 6` orders. The whole range
  is discharged by `GoldenQuorum.wp_ci_loop` — stated for an ARBITRARY
  voter list `ks₀` and an ARBITRARY acked function `ack`, i.e. it is the
  **n-voter** law, not the 3-voter one — through
  `Laws/Range.wp_map_iter_inv`, with ONE generic-iteration obligation
  (`wp_ci_range_body`).

  **INVARIANT DESIGN 1 — the range.** Over the remaining snapshot `rem`:

  ```
  ∃ ks filled,
    ⌜rem = cfgSnapshot ks ∧ (∀ x ∈ ks, x ∈ ks₀)
      ∧ ((ks.map ack) ++ filled).Perm (ks₀.map ack)⌝
    ∗ l ↦ … ∗ lData ↦ … ∗ srt ↦ … ∗ i ↦ ⟨int, ks.length - 1⟩
    ∗ stk ↦ stkArr ks.length filled trail
  ```

  Three decisions, each forced:
  1. **`ks`, a LIST of the voters still to come, not a set.**
     `Array.eraseIdx` preserves order, so `rem` is always
     `cfgSnapshot ks` for the corresponding `ks`, and one step is exactly
     `ks ↦ ks.eraseIdx i` (`cfgSnapshot_eraseIdx`). A set would have
     needed a reachability relation the rule deliberately does not have.
  2. **ONE `List.Perm` carries the whole order-insensitivity.** "What is
     still to come (`ks.map ack`) plus what has been written (`filled`)
     is the full multiset" — and NOTHING says in which order `filled` was
     built, which is the honest state of affairs. The step lemma is
     `perm_eraseIdx_append` (`(l.eraseIdx i) ++ (l[i] :: t) ~ l ++ t`).
     The alternative — a disjunction over reachable states — is 16
     disjuncts at n = 3 and factorial in general; this is one line.
  3. **`i` is pinned to `ks.length - 1`**, the slot the NEXT write
     targets. That is what turns the body's `srt[i] = …` into a
     POSITIONAL write at a prefix length, which is the shape
     `Laws/Values.arraySet_middle` handles at a symbolic index.

  **INVARIANT DESIGN 2 — the sort.** After the loop `ks = []`, so the
  scratch array holds an arbitrary permutation of `[12, 5, 6]`: the
  contents are genuinely undetermined and no invariant can determine
  them. `Laws/Values.mergeSort_eq_of_perm` says `List.mergeSort` returns
  the SAME list on every permutation of its input (given transitivity,
  totality, and antisymmetry ON THE ELEMENTS PRESENT), and
  `mergeSort_intKind_eq_of_perm` instantiates that at the machine's own
  comparison `fun a b => a.1 ≤ b.1` over `(Int × IntKind)` — a relation
  that is NOT globally antisymmetric, which is exactly why the
  antisymmetry hypothesis is membership-restricted. So `slices.Sort`'s
  transition is computed once and the six orders never reach
  `applyStmtOp`. After it the array is the literal `[5,6,12,0,0,0,0]` and
  the rest of the tail (`pos = 3 - (3/2+1) = 1`, `srt[1] = 6`) is
  ordinary walking.

  **NEW GENERAL LAWS/LEMMAS.** `Laws/Values.lean` — entirely
  target-free, no program/lowering/config/acked value in any statement:
  `list_map_eraseIdx`, `list_getElem?_middle`, `list_set_middle`;
  `arraySet_middle`/`arraySet_middle'` and `arrayGet_middle`/`_middle'`
  (the machine's positional read/write at index `pre.length` of
  `pre ++ x :: rest` — what a right-to-left fill loop needs when the
  index is a variable); `normalizeArrayForTy_int` and
  `normalizeValueForTy_intArray` (an array of already-normalized ints of
  one kind normalizes to itself, at ANY fuel and ANY state — without this
  a store into a SYMBOLIC array is unreachable, since `simp` can only
  compute `normalizeArrayForTy` on a literal); `int_normalize_of_range`
  (the signed half of `Laws/Range.int_normalize_of_nonneg_lt`, needed
  because the fill index reaches `-1`); `eq_of_perm_of_pairwise`,
  `mergeSort_eq_of_perm`, `mergeSort_intKind_eq_of_perm`.
  In `Specs/GoldenQuorumThree.lean`: `cfgSnapshot`/`stkArr`/`stkCell`
  and their lemmas, `perm_eraseIdx_append`, `sliceIndexLoc_base`, and
  **`storeLoc_stk_fill`** — one iteration of `majority.go`'s
  right-to-left fill as a store fact, general in the backing array's
  length, the number of unwritten slots, the values already written and
  the untouched tail.

  **TWO SPEC-SURFACE GENERALIZATIONS, both with the old statement kept.**
  `wp_map_lookup_ackedIndex` and `wp_ackedIndex_body` were stated for a
  ONE-ENTRY receiver map — an artefact of the n = 1 walk, not a property
  of Go. Both now have general forms (`…_entries`) over an ARBITRARY
  entry array with the lookup's answer as a `hpair` premise (exactly
  `wp_map_lookup`'s, so no new obligation shape), and the one-entry forms
  are DERIVED from them with their statements byte-identical, via the new
  general `mapLookupValue_singleton`. `wp_ackedIndex_body_entries` also
  hands the receiver's DATA cell back to its continuation — the n = 1
  version dropped it affinely, which is fine when there is no next
  iteration and fatal when there is.

  **A `go_walk` FINDING, worth recording** (it cost an hour and it will
  recur). A law registered `@[go_walk_law]` whose premise is a
  state-quantified SEMANTIC fact gets fired by `go_walk_side`'s
  `assumption` whenever that fact happens to sit in the ambient Lean
  context — so the widened `wp_map_lookup_ackedIndex` started firing
  inside `wp_ackedIndex_body`, the walk ran past the statement the human
  meant to take by hand, and the failure surfaced as a heartbeat timeout
  several steps later. **Rule adopted: a general law with a human-supplied
  semantic premise stays OUT of the table** (as `wp_map_iter_inv` already
  does); what gets registered is a specialization all of whose premises
  are `rfl`/pin facts. That also restores the intended behaviour at the
  general law's own use site: the registered one-entry law matches, fails
  to FRAME its `{q ↦ v}` data cell against an arbitrary `entries`, and
  the boundary rule stops the walk exactly where the general law is
  handed over.

  **GOOSE/PERENNIAL COMPARISON** (verbatim citations). The range-rule
  comparison is unchanged (`wp_map_for_range`,
  `deps/perennial/new/golang/theory/map.v:213`); what this rung adds is
  the *use*. Their invariant is `P keys i` — indexed by a key ORDER
  committed to up front (`∀ keys, ⌜list_to_set keys = dom m ∧ length keys
  = size m ∧ NoDup keys⌝`, :215-217) and a POSITION in it. A proof whose
  final obligation is order-INSENSITIVE (ours: the array's contents
  depend on the fill order, the ANSWER does not) must therefore carry the
  order to the end and quotient it there; our `List.Perm` invariant
  quotients it at the start. That is a proof-engineering difference, not
  a strength claim — their `P keys i` can express order-DEPENDENT
  invariants ours cannot state at all. Second, honestly: **Perennial has
  no model of `slices.Sort`** — `grep -rn "sort" deps/perennial/new/golang/theory/*.v`
  is empty — so the order-blind-sort lemma has no counterpart there to
  compare against; and they handle `break`/`continue`/`return` in ranges
  via `for_map_postcondition` (`map.v:207`) where we still do not (the
  v1 narrowing recorded in phase 1, unchanged).

  **OVER-SPECIALIZATION CHECK, per new law (standing item).**
  `Laws/Values.lean`: TARGET-FREE by inspection — every statement
  quantifies over the list/array/kind/comparison and no program name,
  lowering, config or acked value occurs. `storeLoc_stk_fill`,
  `sliceIndexLoc_base`, `stkArr`/`stkCell`: about a fill loop over an
  array of any length at any position; no `7`, no `3`, no voter. The two
  WALK laws `wp_ci_range_body` and `wp_ci_loop` DO name the pinned
  lowering's statements — they are walks OF the target and cannot avoid
  that — but their DATA is fully quantified: arbitrary voter id,
  arbitrary acked index and snapshot, arbitrary scratch-array shape and
  backing length, arbitrary voter list and acked function. **No voter
  count, no config, no acked value and no `n` occurs in either
  statement**; the 3-voter numbers first appear at
  `wp_committedIndex_body_three`. This was deliberate and is the reason
  `wp_ci_loop` is reusable for ∀-config as it stands.

  **SCOPE, STATED HONESTLY — the ∀-config theorem did NOT land.**
  `committedIndexAllConfigs_statement` remains a target. This is the
  arc plan's recorded fallback line, taken deliberately, with the
  remaining obligations named precisely rather than hand-waved:
  1. **The fit test at general `n`.** `wp_ci_fitIf_three` is the n = 3
     reslice instance; ∀-config needs BOTH branches — the reslice at
     `n ≤ 7` (a `checkSliceBounds`/`sliceFromArray` computation at a
     symbolic `n`) and the `make([]uint64, n)` allocation at `n > 7`
     (`wp_make_slice` exists and is witnessed on that branch, but no
     composed walk goes through it).
  2. **The tail at general `n`.** `wp_ci_tail_three` computes the
     machine's `sortSlice` transition on a 3-slot window by unrolling
     `for i in [:slice.len]`. At symbolic `n` that unrolling is not
     available, so a GENERAL characterization of `applyStmtOp`'s
     `sortSlice` is owed: "loading `n` normalized ints, mergeSorting and
     storing back replaces the first `n` slots by the sorted image". Then
     the readout needs `mergeSort`-vs-`sortAsc` AGREEMENT — both sort the
     same multiset and both are sorted, so `eq_of_perm_of_pairwise` (in
     hand) closes it, but the `sortAsc` side must be lifted from
     `List Nat` (`Specs/QuorumRefSpec.lean`) to the machine's `Int`
     values. Finally `pos = n - (n/2+1)` must be shown to be the index
     `committedIndexRef` reads, at symbolic `n` — the arithmetic
     `quorumSize` already states.
  3. **The encoding bridge.** `EncodesConfig ce c` says the snapshot's
     keys are exactly `c`'s ids IN SOME ORDER; the loop law consumes
     `cfgSnapshot ks`. A lemma turning the former into "`ce = cfgSnapshot ks`
     for some permutation `ks` of `c`" is owed, and likewise
     `EncodesAcked ae acked` ⟹ the `hlook` premise. Neither looks hard;
     both are unwritten.
  4. **The `GoSpec` shell.** The ∀-config target is stated as the
     `GoSpec` at the METHOD with a heap-carried receiver (design (a),
     phase 0), so its discharge needs the caller-environment frame entry
     that `GoFuncSpec2` has and unary `GoFuncSpec` does not — the
     `GoFuncSpec`-with-`argEnv` widening already recorded as OWED at the
     target.
  None of this is blocked on a missing idea; all of it is unwritten Lean.
  The n-voter loop law — the piece the arc plan called "the one that
  makes ∀-config reachable at all" — is done.

  **Gate**: `scripts/ci` PASS. Proofs build + in-build `Audit` sweep
  (6417 declarations, all axiom-clean; new `#guard_msgs` pins on
  `quorumThreeAllFuncSpec`, `quorumThreeAllMeetsSpec`,
  `quorumThreeAllReturnsSix`, `quorumThreeAllNotTwelve`, `wp_ci_loop`,
  `wp_ci_range_body`, `mergeSort_eq_of_perm`, `arraySet_middle`,
  `storeLoc_stk_fill`). `quorumOneKnownFuncSpec`'s statement and axiom
  set are UNCHANGED by the two spec-surface generalizations, which is the
  same acceptance shape phase 2 used. No runtime code was touched (proofs
  only), so no baseline re-pin and no `--diff` re-run is owed.

---

### Build log — 2026-08-01, phase 4: **THE ∀-CONFIG THEOREM — the arc's GOAL, reached**

`Specs/AutomationTargets.committedIndexAllConfigs_statement` — the arc's
exit criterion, a `def … : Prop` written at phase 0 — is **DISCHARGED**
by `Specs/GoldenQuorumAll.committedIndexAllConfigs`. For EVERY voter list
`c`, EVERY acked map `acked : Nat → Option Nat` and every heap snapshot
pair encoding them (`EncodesConfig`/`EncodesAcked`), the PINNED LOWERING
of the real etcd-io/raft `main.MajorityConfig.CommittedIndex` — called on
a heap-carried receiver and a heap-carried `AckedIndexer`, from the
caller's environment — delivers a value satisfying the DECLARATIVE quorum
spec `IsCommittedIndex c acked`, at `GoSpec` strength (triple +
progress, any admissible heap, any frame). The `theorem … : <the def>`
application IS the statement-identity check.

**THE STATEMENT WAS CORRECTED — recorded, not quietly patched.** In its
phase-0 form the target has NO bound on `c.length`, and in that form it
is **FALSE, not merely unproven**: at `c.length ≥ 2^63` the lowering's
`n := len(c)` is a Go `int`, so `IntKind.int.normalize` wraps it
NEGATIVE; `n == 0` is then false, `len(stk) >= n` is TRUE (7 ≥ a
negative), and `srt = stk[:n]` hits `checkSliceBounds`' negative-high
arm — a panic, which `Progress` counts as stuck. The added hypothesis is
`c.length < 2 ^ 63`, a REPRESENTABILITY side condition about Go's `int`
(the same bound phase 3's `wp_ci_loop` already carried as `hsmall`), not
about the target. The falsity is argued, not mechanized — exhibiting the
panicking run at 2^63 entries is a separate cost — and that is recorded
at the target's docstring, in the same shape as the earlier
`quorumAckedIndexFuncSpec2_statement` correction. Everything else in the
statement is byte-identical.

**THE FIFTH OBLIGATION, which phase 3's list did not name.** The four
recorded obligations (fit test at general `n`; general `sortSlice` +
`sortAsc` agreement + the `pos` arithmetic; the encoding bridge; the
surface shell) were all real. A fifth was hiding inside the loop law:
`wp_ci_loop` takes `ack : Int → Int`, i.e. it promises **every voter has
reported**. `majority.go` does not — `if idx, ok := l.AckedIndex(id); ok
{ srt[i] = …; i-- }` skips BOTH the write and the decrement for a voter
with no entry, which is why the missing voters' zeros end up in the LOW
slots and get sorted in among the acked values (exactly `ackedOrZero`).
Every concrete rung so far (n = 1, n = 3) used a TOTAL acked map, so no
walk had ever taken that branch; the ∀-config statement quantifies over
`acked : Nat → Option Nat` with no such promise. This is the
over-specialization check paying for itself: the omission was invisible
to the green gates and to the corpus, and was found by reading the Go.

**WHAT LANDED, obligation by obligation.**

1. **The fit test, BOTH branches** — `wp_ci_fitIf_all`. `n ≤ 7`: the
   on-stack `[7]uint64` resliced (`checkSliceBounds_prefix`, general).
   `n > 7`: `make([]uint64, n)` allocating a backing array of `n` zeros
   (`buildDefaultArrayValue_int`, the machine's default-array `for` loop
   at a symbolic length). The continuation is `∀ ba cap trail, ⌜n + trail
   = cap⌝ ∗ …` — the scratch array's ADDRESS and CAPACITY are
   existential, so nothing downstream knows which branch ran. That is the
   right interface: the branches differ in exactly those two things.
2. **The sort and the readout at symbolic `n`** — `wp_ci_tail_all`, on
   `Laws/QuorumOps.applyStmtOp_sortSlice_ints`: `slices.Sort` over a
   slice of already-normalized ints replaces the visible slots by the
   sorted image and leaves the tail alone, AT ANY LENGTH. `applyStmtOp`'s
   `sortSlice` is two `for i in [:slice.len]` loops over the machine
   state; at a literal length `simp` unrolls them, at a symbolic one
   nothing does, so the loops are discharged by INDUCTION
   (`Laws/Values.forIn_range'_inv`: a bounded `List.range'` fold with a
   step-indexed invariant, stated over an abstract body so the caller's
   actual loop unifies with it). The sort's ANSWER is a premise, and
   `mergeSort_pairs_eq_of_perm` is the usable form: **any sorted
   permutation of the loaded values IS the machine's answer** — which is
   how the reference's `sortAsc` enters, with no `mergeSort`-vs-`sortAsc`
   agreement lemma needed at all (sorted-permutation uniqueness does the
   whole job). `pos = n - (n/2+1)` is Go `int` arithmetic through
   `Int.tdiv`, shown in range and equal to `committedIndexRef`'s index.
3. **The encoding bridge** — `encodesConfig_cfgSnapshot` (an
   `EncodesConfig` snapshot IS `cfgSnapshot` of the voter list it
   carries, and that list is a permutation of `c` — this is where
   `c.Nodup` is used) and `encodesAcked_lookup` (the snapshot answers
   Go's comma-ok pair for `acked` at every voter). The latter needed the
   map-entry SEARCH at a SYMBOLIC entry array: `mapEntryIndex?` is a
   `for … do if … then return i` loop, so `forIn_find_none`/
   `forIn_find_some` (its two shapes, by induction) and the two
   characterizations `mapLookupValue_miss`/`_hit` — the hit form asks
   only that the snapshot be FUNCTIONAL at the key, which is what an
   encoding predicate supplies.
4. **The surface shell** — NOT the owed `GoFuncSpec`-with-`argEnv`
   widening. The target is stated directly as the `GoSpec` it unfolds to,
   and `SurfaceExit.goSpec_of_wp` already takes an arbitrary `env₀`, `P`
   and `prog`: the discharge is `goSpec_of_wp` + `wp_committedIndexCall_all`
   + `wp_value'`, exactly the `quorumAckedIndexFuncSpec2` shape. The
   unary-`GoFuncSpec`-with-`argEnv` widening therefore remains OWED as a
   convenience (nothing now needs it), which is a better outcome than
   widening a surface for one statement.
5. **The missing-voter branch** — `wp_ci_range_body_miss` (one iteration
   that finds nothing: the comma-ok read delivers the `Index` zero and
   `false`, the `if` is not taken, and the law's footprint is only the
   receiver's cells and the key cell — demanding the scratch array would
   be a lie about the step) and `wp_ci_loop_all`, the partial-ack voter
   loop.

   **Recorded duplication.** `wp_ci_loop_all` (partial `ack`) strictly
   generalizes phase 3's `wp_ci_loop` (total `ack`): the latter is the
   former at `ack q = some (f q)`, where `zeros` ends at `0` and the
   `reduceOption` perm collapses to phase 3's. It was NOT re-derived from
   it — that would mean editing `Specs/GoldenQuorumThree.lean`'s green
   3-voter walk for no new claim, and the two laws' proofs share their
   body obligation (`wp_ci_range_body`) already. The derivation is a
   recorded cleanup, not a hidden one: if a third loop law ever appears,
   collapse all three.

**INVARIANT DESIGN — the partial-ack loop.** Over the remaining snapshot
`rem`:

```
∃ ks filled zeros,
  ⌜rem = cfgSnapshot ks ∧ ks ⊆ ks₀
    ∧ ((ks.map ack).reduceOption ++ filled) ~ (ks₀.map ack).reduceOption
    ∧ zeros + filled.length = ks₀.length ∧ ks.length ≤ zeros⌝
  ∗ … ∗ i ↦ ⟨int, zeros - 1⟩ ∗ stk ↦ stkArr zeros filled trail
```

Three changes from phase 3's total-ack invariant, each forced: the
`List.Perm` is over the REPORTED values only (`reduceOption`); the number
of unwritten slots `zeros` is its OWN existential — it is no longer
`ks.length`, because a missing voter shrinks `ks` and leaves `zeros`
alone — pinned to the fill index by `i = zeros - 1`; and `ks.length ≤
zeros` is what keeps the next write in bounds. At exhaustion `filled`
permutes the whole reported multiset and `zeros` counts the silent
voters, so `replicate zeros 0 ++ filled ~ ks₀.map (ackedOrZero)` — one
list lemma (`perm_replicate_reduceOption`), and the sort sees exactly the
reference's multiset.

**NEW GENERAL LAWS/LEMMAS.** `Laws/Values.lean` (target-free by
inspection): `forIn_range'_yield`/`forIn_range'_inv` (bounded machine
loops with a step-indexed invariant, abstract body),
`heap_set_self_of_lookup`, `sliceIndexLoc_prefix`, `list_map_split`,
`intArrayCell`/`intVals`/`sortStage`/`sortStageState`,
`mergeSort_pairs_eq_of_perm`, `reduceOption_length_le`,
`perm_replicate_reduceOption`, `reduceOption_eraseIdx_none`,
`perm_eraseIdx_reduceOption`, `mem_reduceOption_map`.
`Laws/QuorumOps.lean`: `applyStmtOp_sortSlice_ints`,
`buildDefaultArrayValue_int`, `checkSliceBounds_prefix`,
`list_split_first_match`, `valueEq_int`, `forIn_find_none`/`_some`,
`mapLookupValue_miss`/`_hit`. Two existing laws were WIDENED with their
statements otherwise unchanged — `wp_map_lookup_ackedIndex_entries` and
`wp_ackedIndex_body_entries` now carry the comma-ok flag `b : Bool`
instead of a hard-coded `true` (the one-entry registered law
`wp_map_lookup_ackedIndex` and the n = 1/n = 3 walks are unaffected;
their `#print axioms` pins are unchanged).

**OVER-SPECIALIZATION CHECK, per new law (standing item).** Every lemma
listed above quantifies over the list/array/kind/index/monad involved and
mentions no program, lowering, config or acked value. The WALK laws
(`wp_ci_fitIf_all`, `wp_ci_range_body_miss`, `wp_ci_loop_all`,
`wp_ci_tail_all`, `wp_committedIndex_body_all`, `wp_committedIndex_body_empty`,
`wp_committedIndexCall_all`) name the pinned lowering's statements —
they are walks OF the target and cannot avoid that — but their DATA is
fully quantified: no voter count, no config, no acked value. The two
numeric constants that DO appear in statements are the source's own: `7`
(the length of `majority.go`'s on-stack array, which the fit test
compares against) and `18446744073709551615` (`math.MaxUint64`, the
empty-config return). Nothing was shaped by the 3-voter instance: the
concrete data appears only at instantiation sites and in the readout
twin.

**GOOSE/PERENNIAL COMPARISON.** Unchanged where phase 3 recorded it (the
range rule vs `wp_map_for_range`, `deps/perennial/new/golang/theory/map.v:213`).
Two additions, both honest about scope: (a) Perennial still has no model
of `slices.Sort` (`grep -rn "sort" deps/perennial/new/golang/defn/*.v
deps/perennial/new/golang/theory/*.v` finds nothing), so the symbolic-length
sort transition has no counterpart to compare against; (b) the `for i in
[:n]` loops inside `applyStmtOp` are OUR artifact — GooseLang models a Go
builtin as a primitive with an axiomatized spec, where GoCore transcribes
the interpreter's loop, which is what forces `forIn_range'_inv` to exist.
That is the price of the differential-first design (the interpreter is
the spec), and it is paid once per wide op.

**RIDER ITEMS: UNTOUCHED.** Method promotion (BUG-007), the BUG-005
snapshot fix, import-path identity (BUG-010 widening) and type switches
(arc plan §4) were not started in this phase and are not blocked by it —
they are coverage work in the guardrails-first pattern, independent of
the ∀-config theorem. They fall to the coordinator's close-out decision:
either their own slices on this branch or a follow-on arc.

**Gate**: `scripts/ci` PASS. Proofs build + in-build `Audit` sweep (6614
declarations, all axiom-clean; new `#guard_msgs` pins on
`committedIndexAllConfigs`, `committedIndexAllReturnsSix`,
`committedIndexAllNotTwelve`, `wp_ci_loop_all`, `wp_ci_fitIf_all`,
`applyStmtOp_sortSlice_ints`, `forIn_range'_inv`,
`mergeSort_pairs_eq_of_perm`, `mapLookupValue_hit`,
`encodesConfig_cfgSnapshot`). The n = 1 and n = 3 discharges'
statements and axiom sets are UNCHANGED by the two law widenings — the
same acceptance shape phases 2 and 3 used. No runtime code was touched
(proofs only), so no baseline re-pin and no `--diff` re-run is owed.

---

### Build log — 2026-08-01, CLOSE-OUT slice 1: **the layering restructure**

Charter: `docs/2026-08-01_tcb-and-layering-doctrine.md` §2 + close-out
checklist item 1. RELOCATION, NOT RENAMING: every theorem/def name
survives (namespaces are unchanged; only module files moved), so every
Audit `#guard_msgs` pin, witness reference and downstream use compiles
untouched.

**What moved where** (the misplacements the doctrine recorded, all three
eliminated — plus the same class found in two more general modules):

1. `Laws/QuorumOps.lean` is GONE, split two ways:
   - **`Laws/StmtOps.lean`** (general; named for the Go construct — the
     wide-statement `stmtOpK` family): the env/heap algebra, the operand
     walk (`wp_stmt_op_first`/shifts), both apply cores + the allocating
     one (`wp_make_map`/`wp_make_slice`), `wp_sort_slice` +
     `applyStmtOp_sortSlice_ints`, `wp_map_lookup` +
     `wp_read_store_step₂`, the map-range snapshot laws, the map-entry
     search (`forIn_find_*`, `mapLookupValue_miss`/`_hit`), and
     `mapLookupValue_singleton` (general, was stranded in the witness
     section). Imports NO Specs module.
   - **`Specs/GoldenQuorumPin.lean`** (target): the whole `QuorumPin`
     namespace (`rfl` pin projections), the quorum witnesses
     (`wp_map_range_snapshot_committed`, `wp_sort_slice_srt`,
     `wp_map_lookup_ackedIndex[_entries]`, `wp_make_slice_c2`, the two
     dispatch frame-entry witnesses) and `typeEnv_pin_is_load_bearing`.
2. `Laws/Call.lean` no longer imports `Specs/GoldenProgram`: its two
   golden witnesses (`wp_call_enter_inc`, `wp_call_enter_incViaCall`)
   moved to `Specs/GoldenSliceWP.lean` (same `GoLean.Iris` namespace),
   beside the walks that consume them.
3. `Surface.lean` no longer imports `Specs/GoldenProgram`: the step-0
   golden target statements (`outCell0/2`, `goldenDriver`, `outEnv`,
   `goldenOut`, the six `golden*_statement` defs) moved to the new
   **`Specs/GoldenTargets.lean`** (same `GoLean.Surface` namespace,
   Iris-free import chain — it joins the surface-purity scan in slice 3).
   `Surface.lean` is now purely the general judgment language.

**The layer map** is written into `docs/architecture.md` ("Proof-layer
map"): base defs (`GoLean.GoCore.*`) → machine (`Steps`/`execStmt`) →
general laws/lifting/ghost/tactics/surface (`Lang`, `HeapBridge`,
`Ghost`, `Lifting`, `Inversions`, `Laws/*`, `Tactics/GoWalk`,
`Adequacy`, `Surface`, `SurfaceBridge`, `SurfaceExit`) → target layer
(`Specs/*` only: pins, projections+witnesses, target statements, walks).
Direction rule: target uses general, never the reverse.

**The lint** (`scripts/ci`, "import-direction lint", fail-closed): no
module under `proofs/GoLeanProofs/` outside `Specs/` may `import
GoLeanProofs.Specs.*` (root aggregator + `Audit.lean` structurally
exempt), and `Tactics/*` may not import `GoLean` at all. **Zero
exceptions** — the end state the charter asked for; an exception
requires a reason comment in the script and a note in
`docs/architecture.md`.

**Gate**: proofs build green, sweep 6636 declarations axiom-clean, no
new warnings; full `scripts/ci` at the end of the close-out slices.
Proofs-only change (no runtime code), so no baseline re-pin.

### Build log — 2026-08-01, CLOSE-OUT slice 2: **the statement-TCB gate (the deletion test, mechanized)**

Charter: `docs/2026-08-01_tcb-and-layering-doctrine.md` §1 + close-out
checklist item 2 (first half). New `#eval` gate in `proofs/Audit.lean`,
in the axiom sweep's style: for a DESIGNATED list of 20 headline
theorems (the summit family `quorumOneKnown*`/`quorumThreeAll*`/
`committedIndexAll*` incl. `committedIndexAll_refutes_wrong`,
`quorumAckedIndexFuncSpec2`, `recoverFuncSpec`, the five golden
theorems, and `committedIndexRef_meets_spec`), walk the transitive
STATEMENT CLOSURE of each theorem's TYPE and FAIL the build if any
constant reached originates in an Iris module.

**The closure definition, recorded** (the design decision): seed = the
type's constants; every reached constant contributes its own TYPE's
constants; a DEFINITION (`defnInfo` — `def`/`abbrev`/matchers/WF
auxiliaries) additionally contributes its VALUE's constants (the
statement's meaning unfolds through definition bodies); an INDUCTIVE
contributes its constructors (the denoted proposition quantifies over
the inhabitants the constructors determine); a THEOREM/AXIOM reached
contributes its type only (proofs are exactly what deletion deletes).
Iris-ness is MODULE-OF-ORIGIN (`getModuleIdxFor?`, root `Iris`), the
axiom sweep's discrimination — deliberately including `Iris.Std.*`, and
immune to namespace dressing (the tamper test flagged
`Std.ExtTreeMap.instPartialMapCompare`, an Iris-declared instance in the
`Std` NAMESPACE, which an import- or namespace-based check would have
missed). Violations report the full parent chain
(`theorem → def → … → Iris constant`). Fail-closed everywhere: missing
designated name, non-theorem, unresolvable constant, or exhausted walk
budget all fail the build; there is no whitelist.

**Result on the current codebase: PASS** — 20/20 statement closures
Iris-free, per-theorem closure sizes printed in the build log (326–2600
constants; the ~2,000-constant floor is `execStmt`/`Steps` + the
`Std.ExtTreeMap` heaplet machinery the surface judgments legitimately
mean). The doctrine's assessment is confirmed for every designated
theorem. Tamper-tested in both directions: designating
`GoLean.Iris.mapIterInvRule` (whose statement legitimately quantifies
over `IProp` — it is a statement ABOUT the proof infrastructure, and is
deliberately NOT designated) fails the build with 12+ named chains.

### Build log — 2026-08-01, CLOSE-OUT slice 3: **the widened surface-purity scan + exit-criteria bookkeeping**

Charter: close-out checklist item 2 (second half) + coordinator-
delegated bookkeeping.

**The scan** (`scripts/ci`, "surface purity"): widened from its two-file
list to the full statement-bearing set, each file against its OWN
exactly-anchored direct-import allowlist, missing-file behavior still
fail-closed:

- `Surface.lean` — GoLean core + Std only (tighter than before: the
  restructure removed its pin import);
- `Specs/GoldenProgram.lean`, `Specs/GoldenQuorum.lean` — GoLean core
  only (the quorum pin was previously unscanned; added since the
  headline statements unfold through `quorumLowered`);
- `Specs/GoldenTargets.lean` (new, from slice 1) — Surface +
  GoldenProgram;
- `Specs/QuorumTargets.lean` — Surface; `Specs/QuorumRefSpec.lean` —
  QuorumTargets. Every allowlisted GoLeanProofs module is itself in the
  scan, so the Iris-free chain closes by induction, with the GoLean/
  core no-Iris check unchanged as the base case.
- `Specs/AutomationTargets.lean` — **recorded finding**: the doctrine's
  "Iris-free by import chain" assessment was WRONG for this file. It is
  mixed BY DESIGN (the range-rule target quantifies over `IProp`; the
  phase-2 acceptance pins reference proven theorems), so an Iris-free
  chain is impossible and is not claimed. What the gate pins instead is
  its EXACT import list (`GoldenQuorumWP` + `Laws/Range`, nothing else —
  any new import fails), while the Iris-freedom of its pure headline
  targets is certified SEMANTICALLY by slice 2's statement-TCB gate.
  Nothing was whitelisted around the deletion test itself.

A docstring in the new `GoldenTargets.lean` beginning a line with
"import" tripped the widened scan on first run — reworded the prose
rather than loosening the grep (the scan is line-anchored on real
import syntax and prose should not mimic it).

**Bookkeeping**: the arc's Exit criteria are marked MET (∀-config +
3-voter + rule proven; summit re-derived via `go_walk` with identical
statement and axiom set; sweep/gate/ratchet clean), with the rider items
(method promotion BUG-007, BUG-005 snapshot fix, BUG-010 import-path
widening, type switches) moved to a labeled "Deferred to future arcs
(coordinator decision 2026-08-01)" subsection — not started, not
blocked, deliberately excluded from this arc's merge scope. The
remaining exit step is the unconditional pre-merge audit ask + merge
sign-off, with both 2026-08-01 doctrines as named audit dimensions.

**Gate**: full `scripts/ci` PASS end to end at the close-out tip.
