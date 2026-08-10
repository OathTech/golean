# Verdi lane P1 — lane log (2026-08-09)

**Branch:** `verdi-p1` (worktree `.claude/worktrees/verdi-p1`, off `main`
@ `1efa4720`). **Charter:** `docs/2026-08-09_verdi-compat-layer.md` §6 (this
lane is P1), operating under §8b's parallel-lane seam. Mainline runs
concurrently in the primary checkout (`spec-parity-s2`); this lane never
touches it.

## Operating rules inherited from §8b (binding)

- This lane owns `compat/verdi/**` and dated `docs/*_verdi-*.md` ONLY, plus
  its own worktree `deps/` clones. It never touches `GoLean/`, `proofs/`,
  `tools/`, `Corpus/`, `baselines/`, `scripts/`, `CLAUDE.md`, `TODO.md`, or
  the root lakefile/manifest.
- Coordination points (ci wiring, corpus cases, doc-list amendments,
  `proofs/` integration) go on the merge-window queue below — never done
  unilaterally.
- No merges to main from this lane. Small legible slices accumulate on
  `verdi-p1`; the protocol's rebase → gate → audit-ask → ff-only sequence
  happens at merge windows with the user present.
- Every `lake`/`lean` invocation via `scripts/capped`. `#eval` any Bool
  before a decide-family tactic. The compat package builds clean standalone
  at every commit.
- Quality bar: recorded gaps are OK; fail-open behavior and dishonest
  claims are not. The differential harness's failure mode is fail-closed —
  a case it can't judge is a visible refusal, never a pass.
- Nothing long-running (> a few minutes CPU) without noting it here; never
  a full root-lakefile build from this lane.

## P1 scope (from §6, updated by §4d)

(a) **Linearizability vocabulary** (~330 lines) ported into `compat/verdi`
    with the P0 fidelity discipline (verbatim-faithful to the primary
    source; every deviation in the delta ledger below):
    `Linearizability.v:7-270` (K-generic: `op`, `IR`,
    `acknowledge_all_ops`, `good_move`, `IR_equivalent`, `good_trace`,
    `equivalent`), `RaftLinearizableProofs.v:26-93` (`import`, `exported`,
    `get_input`/`get_output`), `log_to_IR`
    (`RaftLinearizableProofs.v:261-270`), `input_correct`
    (`RaftLinearizableProofs.v:994-998`), the
    `CommonDefinitions.v` execute/dedup slice (`execute_log`,
    `deduplicate_log`, `key`, `applied_entries`, `output_correct`), and
    the headline transfer target `raft_linearizable`
    (`EndToEndLinearizability.v:471-478`) as a named `Prop`.
(b) **Differential-execution harness** (design note §3, path 2):
    seed-deterministic generated handler inputs, Lean executable side,
    committed fixture inputs + Lean-computed outputs so the Rocq
    extraction leg can attach later WITHOUT re-implementing the
    generator (the fixture carries explicit serialized inputs, not just
    seeds). The Rocq oracle leg itself: **ATTACHED 2026-08-10** —
    280/280 match; see the parking ledger (resolved) and slice S6.

Out of scope: P2 (rocq-lean-import certification toolchain — network +
version-pin sign-off), P3 (attachment — mainline territory), F5, anything
touching GoCore.

## Provisional D-item defaults (all PROVISIONAL, chosen to be reversible)

- **D1 — PROVISIONAL: standalone `compat/verdi` home.** Keeps the main
  gate untouched; integration under `proofs/` is a merge-window decision.
- **D2 — PROVISIONAL: Lean-native `Nat`/`List`/`Fin`** (the spike's
  choice). Costs slightly heavier Rocq-side isos in P2; nothing in P1
  bakes it in beyond what P0 already did.
- **D3 — PROVISIONAL: P1-differential-only.** No P2 toolchain investment
  from this lane.
- **D4 — RESOLVED (user): downscope**, core fragment first; extension
  rings later, per §4c/§4d.
- **D5 — PROVISIONAL: keep `electoralVictories`** (1:1 fidelity).

## Delta ledger (deviations from the primary source, this lane)

P0's mapping decisions (design note §2) carry over unchanged. New in P1:

1. Coq `import` (`RaftLinearizableProofs.v:26`) → Lean `importTrace` —
   `import` is a reserved keyword in Lean 4. Pure rename; semantics 1:1.
2. Coq `List.remove` → the P0 `removeAll` (removes all occurrences);
   StructTact `remove_all` (`RemoveAll.v:14-18`, deletes a LIST of
   elements) → `removeList`, to avoid clashing with the P0 name. Both
   cited at their definition sites.
3. Coq `sumbool_and (clientId_eq_dec c (fst k)) (eq_nat_dec id (snd k))`
   (in `get_input`/`get_output'`) → Lean `if c = k.1 ∧ id = k.2` under
   the derived `Decidable (· ∧ ·)` — decidable content identical.
4. `acknowledge_all_ops_func`'s `acknowledged_op_dec`/`in_dec` sumbools →
   `if` over `Decidable` instances (propositional decidability, same
   decision procedures). The function stays a FUNCTION on the same
   arguments, target-list semantics preserved.
5. `exported`'s `IU` case binds an arbitrary output `o` never constrained
   (`RaftLinearizableProofs.v:52-55`) — ported verbatim, including the
   unconstrained existential-shaped binder. Not "cleaned up" on purpose:
   the statement must match theirs.
6. `good_trace` is a recursive `Prop`-valued function with a wildcard
   fallthrough; Lean's pattern elaboration splits the same way Coq's
   does (checked against `Linearizability.v:249-255` clause order).
7. Porting FRICTION, not deviation (recorded for the next porter):
   typeclass-projected types (`RaftParams.clientId counterBase`,
   `BaseParams.input …`) are defeq to `Nat` but do NOT reduce during
   `OfNat`/`ToString` instance search — concrete-instance literals must
   be ascribed `(7 : Nat)`, and serializers take `Nat` arguments
   (`serNat`) rather than interpolating projected values. Similarly,
   `exact` on constructors whose premises are `rfl`-equations can fail
   with unassigned metavariables where `refine … ?_` + `rfl` succeeds
   (see `raft_linearizable_conclusion_witness`).
8. Harness generator scope (not a spec deviation): generated INPUT
   states always carry `electoralVictories = []` (no handler reads the
   ghost field); nonempty values still appear on the OUTPUT side via
   `handleRequestVoteReply` victories (7 elected-leader cases in the
   committed fixture). Fixture outputs are COMPILED Lean evaluation;
   the `rfl` witnesses in `Examples.lean` pin kernel reduction on a
   handful of the same handlers.

Recorded gaps (NOT ported, deliberately, this phase): the
`Linearizability.v` proof-side lemma corpus past line 270 (incl.
`get_*_keys` at 272-344, `op_equivalent`, `equivalent_intro` at 1399 —
they are proof machinery for re-proving `raft_linearizable'`, not
statement vocabulary); StructTact `before` and the `TraceUtil.v`
vocabulary (`in_input_trace`, …) used only by the intermediate interface
statements (`OutputImpliesAppliedInterface` etc.), which the END-TO-END
statement does not mention; `prefix_within_term`
(`CommonDefinitions.v:108-114`, invariant-DAG vocabulary, not
linearizability); the ghost/refined layer (P0's recorded gap, unchanged).

## Parking ledger

- **Rocq extraction oracle leg** (P1b's second half). **RESOLVED
  2026-08-10** — leg built and run, 280/280 match (slice S6 below).
  Originally blocked: no Rocq toolchain on the box (`which coqc rocq
  opam coqtop` — all absent, 2026-08-09); never worked around per the
  sandbox/no-install rule. The unpark that resolved it, for the
  record:
  - **Toolchain: Coq 8.18.0** in the repo-local opam switch
    `deps/opam-coq818` (primary checkout; OCaml 4.14.2),
    OPERATOR-INSTALLED 2026-08-10 with user sign-off, repos
    coq-released + **coq-extra-dev** (per verdi's own CI — the
    released coq-verdi does not cover 8.18).
  - **Package revs** (= the repo's standing reading-copy pins):
    coq-verdi @ `7e1641b`, coq-struct-tact @ `97268e1`, coq-cheerios
    @ `5c9318c`, coq-inf-seq-ext @ `601e89e` (installed in the
    switch's `user-contrib`), and verdi-raft @ `a3375e8`
    AGENT-BUILT quick-mode (`make quick`, `.vos`/`.vio`) at the
    primary checkout's `deps/verdi-raft` against those libs.
  - The design-time enable sketch (previously recorded here: opam
    commands with an 8.16 guess) is superseded by the record above;
    version pins were chosen with the user at enable time, as
    required.

## Merge-window queue (coordination points, to be done WITH the user)

1. Wire the compat gate into `scripts/ci` (or a nightly job): build
   `compat/verdi` via `scripts/capped lake build` + run
   `diffharness check fixtures/handlers-n3.tsv` + the `AxCheck` scan.
   Until then the gate is lane-local and manual.
2. `CLAUDE.md` reference-checkout list: no change needed (Verdi pins
   already listed on main); revisit only if pins move.
3. `TODO.md`: record P1-done status and the parked Rocq leg once merged.
4. D1 (move under `proofs/`?) — decide at a merge window, not here.
5. If/when the Rocq oracle leg is enabled: decide where its runner
   lives (`compat/verdi/` script vs `scripts/` — the latter is
   mainline-owned). **Recorded choice (2026-08-10): lane-local,
   `compat/verdi/extraction/build-and-run.sh`** — this lane owns
   `compat/verdi/**` and may not touch `scripts/`; promotion into
   `scripts/`/CI wiring stays a merge-window decision (item 1).

## Slice log (P1 complete, 2026-08-09)

- S1 `12f8a9be`: lane doc.
- S2 `61440180`: K-generic linearizability vocabulary
  (`Linearizability.lean`, `Linearizability.v:7-270` statement slice)
  + `acknowledge_all_ops_func_correct` re-proved + `equivalent`
  non-vacuity witness.
- S3 `d932073f`: `CommonDefinitions.lean` execute/dedup slice
  (`CommonDefinitions.v:27-121`).
- S4 `cd2cb8d5`: `RaftLinearizable.lean` (`importTrace`, `exported`,
  `get_input`/`get_output`, `log_to_IR`, `input_correct`,
  `RaftLinearizableStatement`) + prelude `filterMap`/`removeList` +
  witnesses in `Examples.lean` incl. the named, axiom-checked
  `raft_linearizable_conclusion_witness` (statement-shape only — its
  docstring says explicitly that the trace is NOT derived from a
  `step_failure_star` run).
- S5 `4324710b`: `DiffHarness.lean` exe + `fixtures/handlers-n3.tsv`
  (280 cases, 7 kinds × 40). Fail-closed verified by hand: missing
  fixture → exit 1, tampered fixture → exit 1 with first diverging
  line, unknown args → exit 2. Two cases hand-checked against the
  handler semantics (hAE reject-stale and accept-at-origin paths).
- Every slice: `scripts/capped lake build` green (zero warnings) in
  `compat/verdi` before commit; AxCheck axiom set stayed
  `propext`/`Quot.sound`-only, no `sorry`/`native_decide`/`partial`.

## Slice log — S6, the Rocq oracle leg (2026-08-10)

- S6a `2359f95a`: extraction stub + OCaml replay driver + lane-local
  runner (`compat/verdi/extraction/`: `ExtractRaftHandlers.v`,
  `driver.ml`, `build-and-run.sh`). **Route:** stub compiled against
  the PRIMARY checkout's quick-built verdi-raft `.vos` via
  `coqc -vok -Q .../deps/verdi-raft/theories VerdiRaft` (`-vos`
  compiles clean but DEFERS the `Extraction` side effect — no `.ml`
  emitted; `-vok` loads `.vos` deps and fully processes the file).
  No cross-tree friction; the worktree's own `deps/verdi-raft` stayed
  unbuilt. Coq-side instantiation mirrors
  `VerdiCompat.Examples.counterBase` exactly (nat/nat/nat, init 0,
  handler `i d ↦ (d+i, d+i)`, N=3, clientId nat) via explicit
  `Build_*` constructors — record notation loops in TC search against
  Raft.v's generic `base_params` instance (observed coqc stack
  overflow, recorded in the stub's header). Names: `fin → int`
  (`ExtrOcamlFinInt`), order agreeing with the Lean `Fin`/`allFin`
  mapping via `fin_to_nat`/`all_fin`.
- **RESULT: 280/280 MATCH, 0 diverge, 0 infra** — the Rocq leg
  reproduces the Lean port's output column byte-for-byte on every
  committed case (all 7 kinds × 40). No port bug, no instantiation
  mismatch; the delta ledger gains no entry. Claim scope: handler
  semantics on the fixture inputs, through the extraction TCB
  (nat→int, fin→int, OCaml evaluation).
- **Oracle liveness verified** (a 280/280 that cannot fail is not
  evidence): tampered output byte → DIVERGE exit 1; perturbed live
  input field (reboot `currentTerm`) → DIVERGE; malformed s-expr,
  unknown kind, 3-column row, out-of-range name, header-only fixture
  → INFRA / zero-case FAIL, all nonzero. Driver also round-trips
  every input through its own serializer (grammar drift = INFRA) and
  the runner refuses partial runs (judged-count vs fixture-row-count).
  Two hand-checked insensitive perturbations (hAE `plt`/`t` on a
  reject-path case) produced identical outputs legitimately and were
  not counted as checks.
- S6b `b526861f`: DiffHarness docstring/fixture-header/lakefile-comment
  claim upgrade + header-only fixture regeneration (all 280 case lines
  byte-identical, per the re-pin doctrine); oracle re-run over the
  regenerated fixture: 280/280.
- S6c: this lane-doc record (parking ledger resolved, queue item 5).
- Gate: capped `lake build` green + `diffharness check` 280 cases at
  each slice; extraction artifacts are gitignored and outside the
  Lean build (lakefile targets unchanged).

## The lane-local gate (run before any commit here)

```
cd compat/verdi
../../scripts/capped lake build          # libs + AxCheck + diffharness
./.lake/build/bin/diffharness check fixtures/handlers-n3.tsv
```
Re-generate the fixture ONLY on a deliberate, explained change to the
port or the generator, committed together with the reason (mirrors the
baseline re-pin doctrine) — and re-run the Rocq oracle leg over the
regenerated fixture in the same change:

```
cd compat/verdi/extraction && ./build-and-run.sh
# needs the Coq switch + built verdi-raft theories (parking-ledger
# record); in a worktree without them, point GOLEAN_COQ_BIN and
# GOLEAN_VERDI_RAFT_THEORIES at the primary checkout's. Fails closed
# when absent.
```
