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
    seeds). The Rocq oracle leg itself: **PARKED** — no `coqc`/`rocq`/
    `opam` on this box (checked 2026-08-09), and installs need user
    sign-off (standing rule). See the parking ledger.

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

- **Rocq extraction oracle leg** (P1b's second half). Blocked: no Rocq
  toolchain on the box (`which coqc rocq opam coqtop` — all absent,
  2026-08-09). Never worked around per the sandbox/no-install rule.
  What exists instead: committed fixtures with explicit serialized
  inputs + Lean outputs (`compat/verdi/fixtures/`), format documented in
  `DiffHarness.lean`, so the Rocq leg only needs a parser + extracted
  handlers, not the generator. Exact commands for the user when they
  want to enable it:
  ```
  # (network + install sign-off needed; version pins are the user's call)
  opam init --disable-sandboxing -y
  opam switch create verdi-raft 4.14.2
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam install coq.8.16.1 coq-verdi coq-struct-tact coq-cheerios
  # then: build deps/verdi-raft ('make quick' builds theories),
  # extraction stub per deps/verdi-raft/extraction/vard/, and an OCaml
  # driver that reads fixtures/handlers-n3.tsv, replays the inputs
  # through the extracted RaftNetHandler/RaftInputHandler, and diffs
  # the output column.
  ```
  (verdi-raft's own CI pins: see `deps/verdi-raft/.github` and opam
  files; the exact Coq version pin should be chosen with the user at
  enable time — trust-tools rule.)

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
   mainline-owned).

## Slice log

- S1 (this commit): lane doc.
- S2: K-generic linearizability vocabulary (`Linearizability.lean`).
- S3: raft-side execute/dedup slice (`CommonDefinitions.lean` extension).
- S4: raft linearizability glue + headline transfer target
  (`RaftLinearizable.lean`) + end-to-end non-vacuity witness.
- S5: differential harness (`DiffHarness.lean` exe + committed fixtures).
- (each slice: `scripts/capped lake build` green in `compat/verdi`
  before commit; AxCheck extended as statements land.)
