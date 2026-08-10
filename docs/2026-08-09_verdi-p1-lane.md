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
    320/320 match after the audit fix round (280/280 at attach);
    coverage limits recorded in S6 and the DiffHarness docstring.

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
   (`RaftLinearizableProofs.v:51-54`) — ported verbatim, including the
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
   states always carry `electoralVictories = []` (no message/input
   handler reads the ghost field; `reboot` reads-and-preserves it, so
   its pass-through is exercised only on `[]` — wording corrected at
   the 2026-08-10 audit fix round, which also corrected the coverage
   figure below). Nonempty values still appear on the OUTPUT side via
   `handleRequestVoteReply` victories — in exactly ONE committed case
   (id 194, kind `net`, delivering a RequestVoteReply to a Candidate:
   the fixture's only elected-leader transition; ZERO of the 40
   `hRVR`-kind rows take the winning branch). The original entry
   claimed "7 elected-leader cases" — audit-measured false (the 280
   case rows never changed after S5); the mechanism attribution was
   correct, the count was not. Fixture outputs are COMPILED Lean
   evaluation; the `rfl` witnesses in `Examples.lean` pin kernel
   reduction on a handful of the same handlers.
9. (Recorded at the 2026-08-10 audit fix round; mapping convention,
   not a semantic change.) Coq's standalone eq-deciders `op_eq_dec`
   (`Linearizability.v:11-15`) and `IR_eq_dec` (:22-26) → the derived
   `DecidableEq` instances on the `op`/`IR` inductives (same equality,
   `decide equality` vs derived instance). Their only in-slice
   consumers are `acknowledged_op_dec` and the `in_dec` uses already
   recorded in item 4; the deviation is that the two intermediate
   named constants have no Lean counterparts. Same convention as
   `key_eq_dec` (recorded in `CommonDefinitions.lean`).

Recorded gaps (NOT ported, deliberately, this phase): the
`Linearizability.v` proof-side lemma corpus — which does NOT start at
272 (audit fix 2026-08-10; the old "past line 270" framing concealed
in-window items): unported inside 7-270 are 10 transport lemmas
(`acknowledge_all_ops_was_in` :56, `…_func_defn` :81,
`…_func_target_ext` :104, the five `IR_equiv_*` lemmas :141-190,
`…_func_IRU_In` :263) plus `Section Examples` (:192-247); the only
in-window lemmas ported are `acknowledge_all_ops_func_correct` (:97)
and `IR_equivalent_refl` (:134); past the window the whole 272-1428
corpus (`get_*_keys` at 272-344, `op_equivalent`, `equivalent_intro` at
1399) — all of it proof machinery for re-proving `raft_linearizable'`,
not statement vocabulary; StructTact `before` and the `TraceUtil.v`
vocabulary (`in_input_trace`, …) used only by the intermediate interface
statements (`OutputImpliesAppliedInterface` etc.), which the END-TO-END
statement does not mention; `prefix_within_term`
(`CommonDefinitions.v:108-114`, invariant-DAG vocabulary, not
linearizability); the ghost/refined layer (P0's recorded gap, unchanged).

## Parking ledger

- **Rocq extraction oracle leg** (P1b's second half). **RESOLVED
  2026-08-10** — leg built and run, 280/280 match (320/320 after the
  audit fix round; coverage limits in slice S6 below).
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
   Until then the gate is lane-local and manual. **Audit note
   (2026-08-10): `AxCheck` is ADVISORY** — its `#print axioms` lines
   land in the build log for a human to read; an added axiom would
   print and the build would stay GREEN. The wiring should adopt
   mainline's enforcing pattern (`proofs/Audit.lean`:
   `#guard_msgs in #print axioms` docstring pins per theorem, plus an
   exhaustive `collectAxioms` sweep over own modules that
   `throwError`s — either mechanism FAILS the build on a new axiom).
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
  committed case (all 7 kinds × 40 at the time of this run; the audit
  fix round added the `init` kind and re-ran: **320/320**). Claim
  scope: handler semantics on the fixture inputs, through the
  extraction TCB (nat→int, fin→int, OCaml evaluation). **NO
  DIVERGENCE OBSERVED** — the original "no port bug, no instantiation
  mismatch" wording was qualified at the audit fix round (2026-08-10),
  per the verified findings, to state what the run CANNOT see:
  - the fixture is THIN: single-shot handler calls on independently
    generated random states — no multi-step traces, no election or
    replication sequences, no `Network`/`step_failure` composition;
    hAE leaves the state unchanged in 36/40 cases (log append 2/40);
    exactly one elected-leader transition in the 280 (id 194, `net`);
  - the DEGENERATE counter machine (`handler i d = (d+i, d+i)`,
    symmetric arguments, equal result components) is structurally
    blind to a transposed state-machine application and to a swapped
    `(output, data)` result pair — audit-measured: the machine is
    reached on only 6/280 handler rows, and an `init` mismatch was
    invisible until the `init` kind landed (fix 3: the init:=7 mutant
    oracle now diverges on all 40 init rows, previously 280/280 green);
  - the executable-but-unextracted ported surface (execute/dedup
    slice, `acknowledge_all_ops_func`, RaftLinearizable projections)
    is not covered by any oracle (DiffHarness docstring has the full
    coverage-limits statement).
  Within that scope the delta ledger gained no entry from the run.
- **Oracle liveness verified** (a 280/280 that cannot fail is not
  evidence): tampered output byte → DIVERGE exit 1; perturbed live
  input field (reboot `currentTerm`) → DIVERGE; malformed s-expr,
  unknown kind, 3-column row, out-of-range name, header-only fixture
  → INFRA / zero-case FAIL, all nonzero. Driver also round-trips
  every input through its own serializer (grammar drift = INFRA) and
  the driver enforces the header's cases-per-kind/kinds declaration
  (exact per-kind counts, no undeclared kinds, declaration required —
  audit fix 2: a truncated fixture used to pass the oracle leg green;
  the runner's judged-vs-rows guard was self-referential and stays
  only as defense in depth).
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

## Audit fix round (2026-08-10, pre-merge audit of the lane tip)

The lane's pre-merge audit (14 agents, review + independent verify)
returned ZERO surviving critical/major findings — both filed majors
were DOWNGRADED on verification — plus a batch of confirmed minors and
notes in two classes, claim honesty and driver robustness. All
verdict kernels applied in one fix round; every empirical figure below
is the VERIFIER'S re-measured one, not the reviewer's:

- `39e55412` fix 1 — records/citations: RaftLinearizable.lean's
  drifted cites (six ranges), CommonDefinitions/StructTactPrelude
  off-by-ones, lane doc :88; gap-ledger boundary restated item-wise
  (the 7-270 window is item-selected — 10 unported transport lemmas +
  `Section Examples` sit inside it); delta item 9 added (op_eq_dec/
  IR_eq_dec → derived `DecidableEq`, mapping convention); delta item 8
  truthed (ONE nonempty-electoralVictories case, id 194 `net`, not
  "7"; mechanism attribution was correct; `reboot` reads-and-preserves
  the ghost field, exercised only on `[]`).
- `d3cbd091` fix 2 — driver robustness, negative-tested: oversized
  grammar-valid decimal is now a per-row INFRA (was an uncaught
  Failure abort with no summary); the driver enforces the header's
  cases-per-kind/kinds declaration (a truncated fixture used to pass
  the oracle leg green; declaration-less fixtures refused).
- `af05abb2` fix 3 — the dead `counter_init_handlers` extraction is
  now CALLED: new `init` fixture kind appended after `reboot` (ids
  0-279 byte-identical, verified; fixture 280 → 320, deliberate
  re-pin); the generator's hardcoded "280/280 match" header line
  DROPPED (a generated file must not assert its own oracle status —
  run records live here, not in the fixture); coverage limits stated
  at every claim site without weakening the positive claim.
- This commit, fix 4 — S6 record qualified ("no divergence observed"
  + the blind-spot accounting above), AxCheck's advisory nature
  recorded (queue item 1 carries the enforcing-pattern follow-up per
  `proofs/Audit.lean`), lakefile comment truthed.

Fix-round gate: capped `lake build` green, `diffharness check` 320 OK,
oracle re-run **320/320 MATCH, 0 diverge, 0 infra**; fix-2 negative
tests red as required (oversized decimal → per-row INFRA exit 1,
truncated fixture → per-kind FAIL exit 1, declaration-less → refused);
init liveness: the audit's init:=7 mutant oracle diverges on all 40
init rows (was invisibly green pre-fix).

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
