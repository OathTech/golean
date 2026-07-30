# Arc: proof-corpus catch-up (2026-07-26)

Arc 2 of the sequence (`docs/2026-07-25_arc-sequence.md`). Opens from
`main` @ f64bfc8 (corpus 785/469, untriaged 31, set-ratchet live). The
calculus catches up with the machine: every W-rung merged since the
reshape owes laws and a proof-corpus entry
(`docs/2026-07-24_proof-corpus.md` §5 — whose prediction 1, "the first
non-golden entry will need `wp_call_value_enter`", is precisely the debt
this arc pays).

## In scope

1. **Slice A — the missing law families**, each law + non-vacuity
   witness in the same commit (the standing gate):
   - `wp_call_value_*`: dispatch and frame entry for call-through-value
     (`callValCalleeEnter` with captures prepended — the lambda-lifting
     protocol's proof face).
   - `wp_breakable_*`: enter/done/break (pure-det one-liners; switch's
     proof face).
   - defer: registration (`deferStmt` → callee/args walk → `pushDefer`)
     and the drain step (`frameDeferFall`/`Return` entering the deferred
     body over the rest-of-chain frame).
   - the unwinding family: `panicStmt`/`panicArgK` entry, the generic
     `panicUnwind` strip, `panicFrameEmpty`, the marker completion pair,
     `evalRecover` — almost all pure-det steps (state unchanged), so
     `wp_pure_det` shapes; the stateful one is `panicFrameDefer`
     (enterFrame alloc, mirroring `wp_call_enter_*`).
2. **Slice B — the composition entry**: a `GoFuncSpec` over the
   frontend's ACTUAL lowering of `panic-recover/recover-direct`
   ("returns 7 despite the panic") — closures + defer + panic + recover
   composed in one walk. Requires extending the golden-pin mechanism
   (`Specs/GoldenProgram.lean` + `scripts/check-golden`) to a second
   pinned program.
3. **Granularity ledger**: the chain ops the audits named — the defer
   drain's frame entry, `panicResumeMerge`'s chain append, `clearSlice`'s
   multi-cell zero — appended to the ledger in
   `docs/2026-07-23_reshape-r1r2-machine-design.md` §1.
4. **Manifest update**: entries for what lands here; the still-owed rows
   (W1 multi-result — blocked on the `GoFuncSpec` arity widening the
   manifest's prediction 3 anticipates; W2 switch; W4 accumulator)
   stay recorded as owed rather than quietly dropped.

## Out of scope

- The `GoFuncSpec` arity widening itself (multi-result / `(T, error)`) —
  its own design decision; prediction 3 says it binds first, and the
  honest move is to record where it binds, not to rush it.
- BUG-005/BUG-006 fixes (recorded, scheduled).
- Any new coverage lanes.

## Exit criteria

- Every slice-A law has a witness in the same commit; sweep clean;
  constructive pins intact where they apply.
- The recover `GoFuncSpec` is proven over the pinned actual lowering and
  referenced from `proofs/Audit.lean` (the manifest gate).
- Ledger + manifest updated; gate 12/12; audit ask; merge sign-off.

## Completion record (2026-07-30)

- **Slice A**: landed 2026-07-26 (17 pure-det + 4 stateful laws — the
  2026-07-26 commit message's "16" undercounted by one, and the
  uncounted law, `wp_breakable_done`, was exactly the unwitnessed one
  the pre-merge audit caught; see the audit response below).
- **Slice B**: the composition core landed 2026-07-26 as the
  hand-authored core shape; the arc's stated deliverable — the recover
  spec **over the pinned actual lowering** — landed 2026-07-30:
  `scripts/check-golden` generalized to a pin list (second program
  `GoldenRecover.recoverLowered` + `baselines/golden/recover-lowered.repr`,
  both links verified); `Specs/GoldenRecover.lean` walks the actual
  lowering end to end (`wp_recoverDirect_body`, `wp_recoverCall`) and
  discharges `GoLean.Surface.recoverFuncSpec` — the `GoFuncSpec` form
  the exit criteria name — via the standard exit pipe. One new law the
  actual lowering demanded: `wp_frame_fall_int` (FALL-path value frame
  exit — a recovered function returns normally without `return`;
  witness = the walk itself, same commit). Audit pins + non-vacuity refs
  added; the manifest row updated and the owed twin row retired.
- **Ledger + manifest**: recorded 2026-07-26 (unchanged by slice B — the
  new law's read/store granularity matches `frameReturn`'s existing
  entry).

## Pre-merge audit response (2026-07-30)

3 Opus reviewers (semantics / vacuity / gate-honesty) + refute-by-default
verification: 16 findings, 10 confirmed (1 major, 4 minor, 5 note),
6 refuted. All confirmed findings addressed on the branch:

1. **[major, gate-honesty] check-golden link 1 ran against a possibly
   stale decoder .olean** — the exact drift class the link exists to
   catch could pass in the run that introduced it (link 2 had the build
   hardening since 2026-07-21; link 1 never did; pre-existing on main,
   surfaced by the multi-pin rewrite review). Fix: `lake build
   GoLean.NativeToIR` before the pin loop, fail closed.
2. **[minor, semantics+gate-honesty, one root cause reported by both
   dimensions] parallel runner silent case drop** — `run_case` created
   its `.out` empty up front, so the assembler's absence-keyed fail-closed
   fallback never fired for a worker killed mid-case; the row vanished
   from `latest.tsv` and the tight-loop `coverage-baseline-diff` (no
   `--full`) reported "no regression". Fix: atomic publish (`.out.tmp` →
   `mv` after classification), assembler treats missing OR empty as
   fail-closed, worker-pool exit status surfaced.
3. **[minor, vacuity] `wp_breakable_done` had NO witness** (the one law
   in the family; repo-wide grep found only its definition) and
   **[minor, gate-honesty] the per-law witnesses were anonymous
   `example`s** the Audit reference gate structurally cannot protect.
   Fix: all witnesses are now named theorems; `wp_breakable_done_witness`
   added (empty breakable body falls through, all four laws discharged);
   every witness referenced from `Audit.lean`.
4. **[minor, vacuity] docstring overclaims** — Unwind.lean's header
   ("steps through every law in this file" — it traverses 11 of 21) and
   the Audit block's mirror of it corrected to the accurate split
   (spine walk + named per-law witnesses).
5. **[note, vacuity] `GoFuncSpec`'s binding-point justification cited
   `collectResults`, which does not exist.** Corrected to the real
   mechanism (`Step.frameReturn`/`frameFall` copy `loadMany results`
   into targets; the runner's `runFunctionWithContextM` loads the same
   pinned result locations).
6. **[note, semantics] `panicFrameDeferNil` was validated only by
   reading** (no corpus case drives a nil deferred callee during an
   unwind). Fix: two new cases,
   `panic-recover/nil-defer-during-unwind` (recovering twin, ok/1) and
   `…-abort` (chain-order/head-rendering twin, panic "boom") — both
   PASS; corpus 785 → 787, full baseline re-pinned in this commit.
7. **[note, semantics] `panic-nil-recover`'s guardrail comment asserted
   the opposite of the pinned behavior** (the oracle's GOPATH-mode
   invocation keeps legacy `panic(nil)` semantics). Comment corrected to
   match `panicPayload`'s docstring; program untouched.
8. **[note, gate-honesty] run metadata did not record the concurrency**
   (load-induced timeout drift indistinguishable after the fact). Fix:
   `jobs` row in `latest.meta.tsv`.

Notable refuted findings (kept for the record): the `∀σ`-unsatisfiable
`hnorm` claim for `.defined` types (refuted — the laws are never
instantiated at defined types and the premise is per-instance), the
"typeDefs dropped ⇒ manifest overclaim" (refuted — the pinned programs'
walks never resolve a defined type), and the granularity-ledger-entry
gap for `frameReturn` (refuted — the entry exists).

## Addendum: the parallel differential runner (2026-07-26, user request)

Iteration speed was gated on the sequential runner. `scripts/diff-coverage`
now runs a worker pool: one row file per manifest case, `xargs -P`
(`GOLEAN_COVERAGE_JOBS`, default = core count; `1` restores strictly
sequential execution), per-case result files assembled in MANIFEST ORDER —
the output TSV is byte-compatible with the sequential runner's. The
per-case `lake exe` startup tax (~4 invocations/case incl. the
nondet-oracle re-runs) is gone: the once-built binary is invoked directly,
fail-closed if missing.

Measured on the full 785-case corpus (8-core darwin): sequential 15:24 →
parallel 7:50 (~2×), outputs identical (baseline diff green both ways;
result+stage identity across all 785 rows). The remaining gap is
process-spawn/system time in per-case `go run` harness compiles — future
levers, recorded not built: persist compiled harness binaries keyed on
source hash; batch the frontend emission. The negative lane (309
compile-only checks) has the same shape and is a cheap follow-up if it
ever bottlenecks.
