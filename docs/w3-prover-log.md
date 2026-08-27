# W3 log (2026-08-27) — one writer: the w3 Wave-3.0 worker (same lane, W2's successor)

**Charter**: the campaign worktree's `docs/2026-08-27_w3-charter.md`,
Wave 3.0 (units U3.0a/U3.0b/U3.0c — the interface wave). Contract:
`docs/2026-08-27_w25-invariant-design.md` (ADOPTED by [AGENT]
adjudication; the adjudication itself is a mandatory [USER] review
item at the landing ceremony — restated here so the flag survives).
Branch `w1-prover` @ 849b3707 (inherited; ONE WRITER — W2's worker
retired). Conventions unchanged: capped builds only, box-wide lock
for full builds, zero sorry/native_decide/new axioms, [AGENT]
provenance, derivation-anchored numbers, no subject-run counts in
exported statements.

**QUANTIFIER-AUDIT LINE (the charter's opening requirement):** Wave
3.0 is the INTERFACE WAVE — it advances NO end-theorem quantifier by
itself and says so per unit:
- U3.0a (ghost-acks): interface only — the acks carrier + the
  `certified` instantiation C4's ack clause and W3.2b's
  Match-evidence unit consume. No quantifier advanced.
- U3.0b (readers): vocabulary only — the C3 lens readers with their
  `_ren` congruences; consumed by every clause that mentions the
  checker state. No quantifier advanced.
- U3.0c (the invariant module): the DEFINITION of `I` — the predicate
  whose preservation (W3 body specs), establishment (W3.2f), and loop
  instance (W4) later discharge ∀-states/∀-iterations. Defining `I`
  advances no quantifier; the definition is the contract those rules
  will discharge against.

## Successor re-verification (W2's top claims, re-checked before any work)

All checks run 2026-08-27 against the inherited worktree.

- **Tip + cleanliness**: `git log` head = `849b3707` ("W2 gate
  record… branch-complete"), `git status` clean. CONFIRMED.
- **Gate log on record**: `artifacts/w2/ci-gate.log` tail =
  `RESULT: PASS`, `GATE_EXIT=0`. CONFIRMED.
- **Hatch grep**: `grep -rn "sorry\|native_decide" proofs/GoLeanProofs/`
  → doc-comment mentions only (6 docstring hits, 0 live). CONFIRMED.
- **The two retained witnesses are in-build**: `NativeS1Witness` /
  `NativeS23Witness` imported by `proofs/GoLeanProofs.lean` (lines
  63/65) — the standing non-vacuity gauges this wave must keep green.
  CONFIRMED (build-enforced).
- **Box-wide build lock**: owner file reads RELEASED (W2's exit,
  09:23Z); zero lake/lean batch processes on the box. CONFIRMED.
- **W2 gate artifacts spot-check**: `w2_gate` present at
  `Specs/RaftPilot/W2Gate.lean:282` with the composition exactly as
  logged (CallSpec + FrameSim + callSpan_plug + absRaftNode_frameSim);
  `Audit/W2.lean` present and imported. CONFIRMED by reading.

Verdict: W2's record stands as claimed; work begins from 849b3707.

## Judgment calls and checkpoints

(one-line [AGENT] entries appended per decision; checkpoint block
after each unit)

- [AGENT] Sandbox note: /tmp is write-only in this session's sandbox
  (`nono why`: read denied); build logs go to repo-local
  `artifacts/w3/` (the predecessors' convention anyway). No
  workaround of the sandbox attempted.
- [AGENT] U3.0a shape: acks entries are `(term, ackedIndex)` pairs,
  per-acker (`acks : Nat → List (Nat × Nat)`, the exact `votes`
  mirror); `ackCertified voters g tm idx` = ∃ quorum, each member has
  an ack `(tm, k)` with `idx ≤ k` (prefix-acknowledgement reading —
  matches the note's "recorded at ≥ the index"). The EStep/HStep
  wiring is TRANSPARENCY + the named instantiation, not new
  constructors: `EStep` provably never writes acks
  (`EStep_acks_eq`); `HStep`'s abstract `certified` parameter keeps
  its shape and `ackCertified` is documented as its intended
  instantiation (performed at W3.2b, not here). Extending EStep with
  an AppResp constructor was NOT done — the election fragment has no
  AppResp step, and inventing one here would reshape the S1 dialect
  the discharge layer is proved against.

## U3.0a — THE GHOST-ACKS EXTENSION: LANDED

- Files: `Specs/Raft/NativeObligations.lean` (Ghost + `acks` field;
  `ackCertified` + `ackCertified_mono` + `ackCertified_le`),
  `Specs/Raft/NativeEtcdDischarge.lean` (`pushAck` + self/other/
  votes/victories frame lemmas; `pushVote_acks`/`pushVictory_acks`;
  `mem_acks_pushAck`; `EStep_acks_eq`; `ackCertified_estep`),
  `Specs/Raft/NativeS1Witness.lean` (wG0 acks field; WITNESS 4
  `witness_ackCertified` — ackCertified inhabited via two pushAcks at
  the twin's 2-of-3 shape; WITNESS 5 `witness_acks_transparent`).
- Quantifier line: interface only; advances no quantifier (stated in
  the Ghost docstring).
- **The two retained interface witnesses re-run and GREEN** after the
  extension (NativeS1Witness / NativeS23Witness rebuilt in the same
  target set; no witness claim changed — the S1 witness gained two
  NEW theorems, its existing four steps + three witnesses untouched).
- Build: `lake build GoLeanProofs.Specs.Raft.NativeCheckerBridge
  …NativeS1Witness …NativeS23Witness` capped 48G/4 threads →
  EXIT=0, 28 jobs (artifacts/w3/u30a-build.log); `Audit.CheckerBridge`
  pins EXIT=0 (u30a-audit.log). Wall: ~1 min class (warm imports;
  the 28-job log's own duration — no single module above seconds).
- No Audit pin changes; no trust-surface files touched.
