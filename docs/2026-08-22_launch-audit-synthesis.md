# The whole-stack launch audit: synthesis and fix-round ledger

Date: 2026-08-22. Audit tip: `5f5642eb` (tree clean throughout; every
reviewer and verifier read-only, scratch under `.tmp/wsa-*`).
Structure: the dossier's proposal (`docs/2026-08-21_launch-audit-dossier.md`
§4) — nine decorrelated reviewers, one per dimension, fed dossier §3
only — plus a tenth broad-brief "noodler" mandated by Mike ("go
anywhere, poke at whatever seems suspicious"), then three refute-default
verifiers on the top findings. Reviewers D1–D10; verifiers V1–V3. Full
reports are in the session transcript; this note is the durable record
of what survived, what was refuted, and what the fix round does.

## 1. The verdict

**The object-level stack held.** The semantics, the envelopes, the
statements, and the proof layer came through independent adversarial
probing without a single confirmed defect:

- **D1 (semantics, 41 fresh differential probes through the real
  pipeline)**: arithmetic/conversion edges 9/9 bit-exact, panic/defer/
  recover composition 10/10, containers 10/10, interface dispatch 9/9,
  chan/sync HB layer faithful to every go_mem sentence on deep read.
  Every divergence traced to an already-registered row; **no new
  defect class**.
- **D2 (envelopes)**: all 9 ChoiceSite envelopes PASS, 8/8 spec quotes
  re-verified verbatim against the pin; every recorded narrowing found
  at every consumer.
- **D8 (over-specialization)**: the drift hypothesis **refuted** — the
  choice-site set is exactly the enveloped latitude rows; the pinned
  holes are NOT explained by target need (raft heavily exercises 6 of
  the 7 tier-1 holes); corpus 5.8% raft-attributable; statements clean;
  zero derive/subject leakage into general tooling.
- **D4 (statement TCB)**: holds on the designated set; latent
  gate-scope findings only.
- **D6 (instruments)**: no reachable fail-open, no vacuous ratchet;
  the Audit sweep verified genuinely closed over all 26 core modules;
  step 1c4's landmark logic verified correct including its would-have-
  fired history.

**The surviving findings concentrate in four places**, none of them the
machine's semantics: one frontend name-resolution bug (D10-F1, the
audit's only silent-wrong-answer finding), the records/meta layer
(register staleness, the constitution append), one relocatable GoCore
node (D8-F1, downgraded), and a set of small gate hardenings.

## 2. Confirmed findings and their dispositions

Severity after verification. **FIX** = this fix round; **ARC** = its
own later arc; **REC** = record-only.

| finding | verdict | disposition |
|---|---|---|
| **D10-F1** shadowed predeclared `true`/`false`/`nil` mis-lowered as literals (`emit.go` emitIdent name-switch ahead of go/types) | V1: CONFIRMED **and understated** — also wrong via shadowing *parameters*, silent wrong `len` of a slice-valued `nil` shadow, one fabricated panic | **FIX**: BUG-069; delete the `true`/`false` arms (const-fold already emits the identical node), universe-guard `nil`; guardrail family `scoping/predeclared-shadow` (8 rows) |
| **D8-F1** `sortSlice` is a target-shaped GoCore node | V2: confirmed in substance, **downgraded CRITICAL→MAJOR** ("only non-language ctor" false — the `sync` family is stdlib but *inexpressible in source Go*, which sortSlice is not; nothing fails open; remedy is a flagship-proof redesign ~500 lines, not a relocation) | **ARC** (post-launch, parallel lane). **FIX** for the cheap record items: U-5 gains `sortSlice`; SortFunc tie-order latitude registered; extern-policy note annotated superseded |
| **D5-F2 / D7-C1** dossier §3 stale at birth (V3: 13 rows verified, mechanism = parallel-lane observation lag, all safe-direction; also omits W4.3's NEW residuals) | V3: CONFIRMED | **FIX**: stale rows corrected in place + a new-residuals addendum; method noted in the dossier header |
| **D5-F4** the twin never leaves term 1 (V3 re-ran the battery: all 9 schedules `claims=1`, states ⊆ {F0,F1,C1,L1}, S1's disagreement branch dead; raftharness demands minClaims=2 on 4/6) | V3: CONFIRMED | **FIX**: one term-2/step-down schedule added to the twin battery; bound recorded |
| **D5-F3 + V3** machine-tier numbers (26/27, 131/148) measured 12 frontend commits before tip; the recorded re-run was `--no-machine` (structurally blind to the frontend change class) | V3: CONFIRMED (line true when written, stale at HEAD) | **FIX**: full machine-tier re-run at the fix-round tip, detached; log line corrected |
| **D5-F1** the p2 verdict aimed at a deleted inode (worktree pruned under the live run) | — | **rescued live**: detached readers hold the inode; report lands in `.tmp/p2-recovery/` |
| **D9 C-1..C-3** constitution ratified by *append* (§8.1) instead of in-place amendment per §4.5; DRAFT banner + [MIKE] holes in governed text; §5 Plan A contradicts the ratification | — | **FIX**: fold-in-place (see §4 below for the rulings folded with it) |
| **D6-F1** `Pinned-by:` not fail-closed in check-bugs (typo silently exempts; the exact hole closed for `Status:` in July) | fixture-probed by D6 | **FIX** (one line + fixture re-probe) |
| **D10-F4** no mechanized `go version` check anywhere against the 1.26.5 oracle pin (incident precedent: the `1.26.x` float) | — | **FIX**: preflight in `diff-coverage` + `scripts/ci` |
| **D6-F2/F4** preflight `/-` comment hole; three attribute spellings escape the meta-hatch scan (`@[simp, implemented_by]`, split-line `unsafe`/`opaque`) | fixture-probed by D6 | **FIX** (pattern hardening + fixtures) |
| **D6-F3** two count-guards missing the house non-empty assertion (`check-imported-pins` PINS, ci `evok`) | — | **FIX** |
| **D6-F6** `LANDMARK-RUN:` marker is hand-pasted prose, not emitted by the judge | — | **FIX**: judge emits it |
| **D1-F1** min/max-len witnesses | V1: reproductions exact, framing **refuted** — BUG-062's already-pinned shape rewrapped; the genuinely unpinned axis is grossmith F-1's call-*outside* shape (already blocking as G-18/C-9) | **FIX**: the five offered `builtins/min-max-vs-call-order` rows pinned (3 RED + 2 GREEN controls); BUG-062 statement widened per findings-2 §9 F-1 |
| **D1-F2** assertion-vs-call witness | V1: divergence real, "first witness" **refuted** (E13 already carries two; census-only, "NO PIN MAY BE TAKEN HERE") | none (register correct as-is) |
| **D1-F4 / N-13** Race.lean:617-622 stale ChanClocks docstring | confirmed unfixed | **FIX** (doc comment) |
| **D8-F2** W7 K2 register under-tags B-20/B-21 (refuted by B-19's own spec quote) and C-35 (same E4 axis as K2-tagged C-36); receiver-operand order uncensused | — | **FIX**: retags + a census-only receiver row |
| **D10-F2/F3** wire decoder: out-of-range int literals two's-complement wrap; duplicate JSON keys last-wins (`Json.parse` dedupes pre-StrictJson) | — | **REC**: added to the H-c decoder-check family (unreachable from the honest frontend; H-c's disposition) |
| **D2-F5** print-interleaving: a wedge-class candidate inside register #5's residual (soundness condition false at that shape, unpinned) | — | **REC**: routed to slice 5 with the U-1 pattern (directed probe + membership row) |
| **D3-F-4** ratified S2/S3 prose vs the harness's non-empty-EntryNormal projection | — | **FIX**: option (b) — projection declared in §2.2.2 fine print with the widening obligation and the why |
| **D5-F5/F6** no executable instance of §2.1's ∀-stream shape over the subject; the twin's Lean side is greenfield | V3: CONFIRMED (an informal single-stream ∃-witness exists) | **REC**: stated in the constitution's evidence-status fine print so the first proof arc starts from facts |
| **D6-R1/R2** CI on branches never runs the differential (`GOLEAN_ALLOW_NO_DIFF=1` on push/PR); corpus source bytes outside every fingerprint except the slow tier | — | **deferred** (needs design, not launch-blocking; recorded here) |
| **D7-C2** I-2/E12 interpretation contradiction; D7-M* cite fixes; D2-F1..F4, D3-F-1/2/3/6, D9 items 1-12, D4-F1..F5 | various | **FIX** where mechanical (cites, docstrings, pointers); the D4 gate-scope items land with group C |

## 3. What the structure missed that the noodler caught

Mike's question, answered: D10 found the one defect the nine structured
dimensions could not — D1 probed the *semantics* adversarially and
found it clean, but only a broad-brief probing of the *frontend's name
resolution* with programs no idiomatic corpus contains (shadowed
predeclared identifiers) reached BUG-069. The lesson for future audits:
keep a noodler in the roster; the frontend's oldest untouched paths are
where corpus-blind classes live.

## 4. Rulings (Mike, 2026-08-22)

- **E-1 (launch gate exit)**: the gate is "pause before launching, and
  Mike signs off." Nothing more formal; no severity thresholds, no
  waiver machinery. (Mike explicitly declined the formalization —
  "gate cruft showing up in another guise"; guardrails will not be
  perfect and looseness is wanted.)
- **General directive**: pre-build fine-tuning is to be avoided; only
  blockers get decided up front; minor decisions are relitigable later.
  Applied: D3-F-4 takes the doctrine default (narrow + declared +
  widenable); the surgery-threshold line (O-6/O-7) is written in as the
  recommended split (oracle-divergence bugfix with red pin first =
  allowed; envelopes/choice sites/granularity/new nodes/observation
  notion = park for Mike) subject to Mike's veto at the fix-round
  merge; E-2 dissolves into standing practice (milestone claim = gate
  green at the claiming tip + derivation-anchored numbers in the
  campaign log); compat/verdi stays a read-only reference — the
  campaign ports proof *structure* as ideas, not code (same policy as
  refinedc/Lithium, Mike 2026-08-22).
- **sortSlice**: post-launch parallel-lane arc.
- **Machine re-run**: full, detached, at the fix-round tip.
- **Twin term-2 schedule**: added in this round (non-vacuity: S1's
  detector must be exercisable before the campaign pins it in Lean).

## 5. The ratified launch plan — retrospective record (D9's gap: the
plan existed only in chat)

Ratified by Mike 2026-08-21 ("Great, let's do it! consider this plan
ratified"), four parallel lanes staging everything up to the
whole-stack audit; all four landed before the audit ran:

- **Lane A — the corpus train (W4.3/W4.4)**: the trace differential
  milestone; landed at `35b18794` (558 blocks, 354 supported, OK
  206/206, RENDERED 148/148, machine tier 26/27; BUG-068 found by the
  rendered tier) after its own 4-reviewer audit + fix + delta-review +
  convergence rounds.
- **Lane B — slice 5b**: the second PL-nitpicker review of the
  semantics design; landed `a6f1ae90`.
- **Lane C — the Q-row memos**: the eight W3.2 design questions
  memo'd for one-sitting ruling; landed `fe7fd2c1` (implementations
  explicitly post-launch).
- **Lane D — the audit-prep dossier**: the claim-chain map, the §3
  residuals register, `tools/reconcile-records`, and the audit's
  proposed structure; landed at `42fae106` with the settlement.

The audit itself ran per the dossier's structure + Mike's added
noodler; this document is its synthesis; the launch gate's exit is
Mike's sign-off after this fix round.

## 5b. Fix-round execution record (2026-08-22, lane `launch-fixes`)

Every **FIX** row in §2 landed on this branch; the per-commit map is
the branch log itself (guardrails-first ordering: pre-fix colors
committed before the emitIdent fix; baseline re-pinned from the full
`--diff` run in the same arc — 2475 = 2303 PASS / 172 FAIL, drift =
exactly the 13 entrants, zero movement on the 2462 prior ids;
`wrong-answer 0/0` restored honest). Gate state at the tip:
`scripts/ci` fast PASS; the full `--diff` PASS at the re-pin commit;
`scripts/comparator-judge` PASS — 56 theorems, 417s, fresh clone @
`1730567a` (the widened trigger fired on the four trusted-closure
docstring moves, correctly; the marker was emitted by the judge's new
mechanical append, its first live run). The twin battery re-verified
both-oracles PASS including the new `stepdown-reelect` schedule
(term 2 reached, step-down exercised, claims=2, full trace
agreement). IN FLIGHT at arc-complete: the full 27-trace machine-tier
re-run at this tip (detached →
`artifacts/launch-fixes-rerun/machine-tier-full.txt`; the D5 5-trace
spot check at the audit tip already agreed byte-for-byte) and the
`95145bc3` p2 rescue (`.tmp/p2-recovery/`). Consciously NOT done
here: the campaign's first-week items from D9 (worker-brief template
collection, the `refined_raft_net_invariant` port) — campaign work,
not fix-round work.

## 6. Deferred (recorded, not launch-blocking)

- The sortSlice relocation arc (V2's costing: frontend trivial; the
  flagship's one-lemma symbolic-length sort step becomes a verified
  in-place insertion sort — a new proof shape, ~500 lines; plus a
  golden regen, a baseline re-pin, one red pin flipping green, and the
  named-slice-type narrowing lifted in the same change).
- D6-R1 (branch CI runs no differential) and R2 (corpus bytes
  unfingerprinted) — gate-design questions for a later gates arc.
- grossmith F-3 (UNSEQ non-call-operand inventory row) — already owed
  from findings-2; unchanged.
