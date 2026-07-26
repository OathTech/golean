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
