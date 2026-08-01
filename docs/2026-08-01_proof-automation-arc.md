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
