# Adversarial pre-merge audit: stray-panic refusal (packet A audit F1 fix), 2026-09-27

[AGENT] auditor (Opus 5.5 subagent). This audit runs under the [USER]'s standing rule that every merge is audited
adversarially (relayed). Candidate: `core/stray-panic-refusal-0927` @ `05d0dbd4` (runtime `9862be1c`) over `main` @
`7d2a62e5`. Audit branch: `review/stray-panic-refusal-0927`, which holds this note and
`docs/evidence/2026-09-27_stray-panic-refusal-audit/` and nothing else. The candidate is untouched. Nothing was
merged, pushed or tagged. Scratch worktrees (not committed): `audit-stray-panic-main` (detached at main) and
`audit-stray-panic-pa` (detached at `36d8571b`, which is packet A's tip rebased on this candidate; its
`GoLean/GoCore` equals the candidate's apart from the two added statement files `BridgeSet.lean` and
`ExecutionStatement.lean`).

## VERDICT: MERGE-CLEAN

The fix does what it says. On every root location the new reader is `loadLoc`, both definitionally and
empirically: access traces are byte-identical to main over 3724 corpus rows × 2 streams and over 5 new frontend
probes. The six sites are the complete class. No lowered program can reach the new refusal. The relation moved in
step with the interpreter, and the proofs build unchanged. The gate is red on exactly the 5a pair. The F1 witness
is now the named `.internal` refusal. It is classified by `ClassRefusal` and excluded by `NoRefusal`, and all
three facts are proved in Lean. The findings below are LOW or NIT and none blocks the merge.

## Findings

- **A1 (LOW, follow-up; not this lane's class).** The drivers' post-termination readout `loadMany`
  (`StepFn.lean:997`, `:1215`; `Multi.lean:2065`; `CLI.lean:885`, `:893`, `:1266`; `EnumSpec.lean:62`) still reads
  the pinned result cells through `loadLoc`. On a non-root pinned cell, an out-of-range index would surface as a
  `.panic` from the readout and be reported as a Go panic. This path is outside `stepFn`, so it is not in the
  packet A statements over `execStmtLoop`, and it is unreachable for the reason the lane records: `pinResultLocs`
  reads an env whose bindings are all `Store.alloc` roots. Because it is the same read of the same cells, it could
  go through `loadRoot`. That is an [AGENT] suggestion, and it is a trust-surface edit for a later lane, not
  this merge.
- **A2 (NIT, controls).** The S5 positive control that the lane note lists as missing is now supplied as
  `s5_positive` (`StrayPanicRecheck.lean`, `rfl`). A root guard test binder holding `true` against `when = true`
  gives `.ok ([.done], s1, [read (base 0)])`: same store, one read at the root.
- **A3 (NIT, evidence cosmetics).** In `results.txt` the probe observations are split at the JSON's `\n`, because
  zsh's `echo` interprets escapes. The values are intact.

## Attack record

1. **No semantic change on reachable programs.**
   - Definitionally, `loadRoot (.base _) = loadLoc (.base _)`. `Mem.loadBinding` and `Mem.loadBindingFor` build the
     same label as `Mem.load` and `Mem.loadFor` (`[.access .read (.data l.canon)]` and `(… leaf.canon)`), and the
     same `projChainTarget` leaf is passed at S6.
   - Empirically, the harness `AccessDump.lean` was built once against each tree. It folds every step's label,
     both the init-phase `stepFn` traces and the pool's `StepEvent.who|trace`, plus the status, the step count and
     the output. It ran over every manifest row with a wire: 3725 rows, of which 3724 were traced, each under 2
     streams, giving 7448 lines per tree. The two outputs are IDENTICAL (sha256 `4d2c0c23…`). The coverage includes
     108 evalorder/unseq rows, 98 panic-recover rows, 124 functions/named rows, 79 race rows and 167
     goroutine/channel rows. The refusal text occurs 0 times.
   - One row, `strings/trimspace-repeat/repeat-bound-refused`, is excluded: my harness overflowed its stack on BOTH
     trees.
   - S1 was checked on its own. `loadMany` and `loadResults` read the same cells in the same order. On a `.base`
     cell each is `loadLoc`, with the same first error. Only the result, or the error, of the bind matters: a
     successful bind is followed by the `throw`, so there is no successor and the trace is discarded either way.
     The old `stuck "extra GoCore assignment value"` therefore fires under exactly the old condition, which is
     "all root reads succeed". The lane's own S1-positive control pins that. The only behaviour change is on
     non-root cells, where the old outcome was a stuck refusal, an escaped panic (the bug) or the same stuck
     message. The relation has no rule for a targetless frame exit with results (`Machine.lean:5652`), before or
     after the fix.
2. **Completeness of the six sites.**
   - I re-derived the census independently. The `←` binds in `stepFn` that are not wrapped in `toResult`
     (`StepFn.lean:160`–`997`) are exactly the investigation's list.
   - Every remaining `loadLoc`/`Mem.load*` either reads an address VALUE under a `toResult` apply (`applySlice`,
     `indexLoc`, `len`/`cap`, `applyAtomicOp`, `syncCell`, `unseqReadTarget` via `unseqLoad.plan` under
     `toResult`) or is a peek whose error is absorbed as a non-narrowing (`projChainTarget` and
     `unseqUnfrozenAnchor?` pattern-match `.ok`).
   - The normalizer and zero-value descent (`Ops.lean:1100`–`1260`, `:2185`–`2245`) contain no panic.
     `valueAsMap`, `mapPayload?` and `unseqCellLoc` fail only with stuck.
   - Legitimate non-root bindings: none exist. `LocalEnv.declare` has four executable callers and all bind
     `Store.allocCell`'s `.base` (`Store.lean:36`). No other code constructs an env.
   - Five frontend probes covered named results aliased by `&` under defer and recover, a named struct and array
     result with field/element addresses, method values on `&arr[i]`, per-iteration range and loop variables with
     their addresses and closures, unseq multi-assign (`i, a[i] = …`, `m[k] += f(&k)`, struct and array swaps), and
     a goroutine with a named-result defer plus a recovered out-of-range write. All five agree with `go run` on the
     candidate and on main, their traces are identical, and no refusal appears.
3. **Coherence.**
   - `Step.evalVar`'s premise is `Mem.loadBindingFor`, which is exactly the `stepFn` arm.
     `frameReturnTargets`/`frameFallTargets`, `unseqComplete`, `unseqRunTarget` and `unseqRunGuard` call the shared
     helpers (`Machine.lean:5662`, `:5666`, `:6066`, `:6115`, `:6120`).
   - `MachineSound`/`StateWf` and the other coherence modules are unchanged apart from the four `StateWf`
     consumers. The whole library builds (ci "core build (warning-free)" ok) and `check-core-audit` is green.
   - The bridges `loadRoot_ok`, `loadBinding_ok` and `loadBindingFor_ok` are true one-way implications: success of
     the stricter reader implies success of the old one with the same result. They do not weaken any invariant.
   - There are no new escape hatches (ci preflights ok).
4. **Call-site check.**
   - Adding `loadRoot` to `RAW_OPS` makes the check stricter.
   - The new rows are correct: `loadRoot`←`loadLoc`, `Mem.loadBinding(For)`←`loadRoot`, and `unseqStorePlan`
     now on `loadRoot`.
   - Removing the `stepFrameExit/loadMany` row is justified: the arm now calls the emitting `loadResults`.
   - `check-mem-callsites` ok in the gate.
5. **Controls.**
   - All 11 `strayPanicRefusalFacts` are `ok` in the gate's eval tests.
   - The negatives drive S1, S2 and S6 through `stepFn` and S3, S4 and S5 through the exact helpers `stepFn` binds.
     `stepFn` calls those helpers directly (`StepFn.lean:242`, `:278` via `unseqTargetPlan`→`unseqAtoms`→`unseqAtom`,
     and `:282`).
   - The positives check values AND labels for S6, S2 and S4, the old stuck refusal for S1, and the values for S3.
   - The S5 positive is added here (A2).
6. **Packet A's refuted statements** (`StrayPanicRecheck.lean`, `lake env lean` at `36d8571b`, EXIT=0, axioms
   `propext`/`Classical.choice`/`Quot.sound`). Each check was `#eval`ed first. The results:
   - The F1 witness's `stepFn` and `execStmtLoop … 1` both return `.error (.refusal (.internal "binding cell is not
     a root location: …"))` for every tape.
   - `witness_classRefusal` holds.
   - `witness_not_noRefusal` holds, so the witness no longer meets `classification_wf_stmt`'s premise.
   - `witness_not_panic` holds.
   - The packet A audit's original refutation file no longer elaborates (`step0`/`loop1` are "not a definitional
     equality").

   In my assessment, [AGENT], not proved, the four statements `finish_abort_step_stmt`, `run_panic_iff_stmt`,
   `classification_stmt` and `classification_wf_stmt` are now TRUE. The census in item 2 leaves the abort arm
   (`StepFn.lean:386`) as `stepFn`'s only `.terminal (.panic _)`, and the stray is now a refusal, which
   `ClassRefusal` classifies and `NoRefusal` excludes. The proofs remain packet B's.
7. **Gate.** Under the box-wide lock, `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at `05d0dbd4` gave
   EXIT=1 in 801 s, which is the expected red on EXACTLY the 5a pair:
   - `certificate provenance` is STALE (changed dependency `Machine.lean`).
   - The single drift line is `imported-goose/channel/google-search` PASS→FAIL/membership, over 3768 rows.
   - Every other step is ok, including the negative baseline (no regression), core-audit, mem-callsites, the unseq
     scheduler/wire and eval tests (285 ok). Tail: `ci-diff.tail.txt`.

## What I did not verify

- I did not prove packet A's four statements (item 6 is an assessment).
- I did not re-audit every helper transitively called under `enterFramePickV`. I relied on its internal
  classification, as the investigation did.
- The 43 manifest rows without a wire (frontend refusals) were not traced, nor was the one excluded row.
- The trace comparison used 2 streams, not the full membership enumeration.
