# t1-fidelity-fixes — lane report (Tier-1 fidelity round + pre-merge audit fix round)

Record honesty batch [AGENT], written at the audit fix round
(2026-09-01) per the auditor's ordering; this file is the tracked
carrier for the certifying numbers, the flip-taxonomy correction, the
commit-message errata, the fileOrder-consumer resolution, and the A-4
re-pin guard exercise. The audit report itself was delivered as the
fix-round task brief; its probes are preserved (gitignored) under this
worktree's `.tmp/audit/` and were re-run to verify every fix below.

## 1. Certifying runs

- **56ebcde9** (the Tier-1 round's final tip, pre-audit):
  `scripts/ci --slow` PASS, **2489/2489** manifest cases classified,
  full re-certification of cached records. This is the run ca46f8ac's
  message promised ("Full ci --slow at this tip follows") — the
  PASSING run happened at 56ebcde9; see errata (e3) for the run
  ca46f8ac itself referenced.
- **Audit fix round tip** (this commit): `scripts/capped scripts/ci
  --slow` **PASS rc0**, 280.9s elapsed (979% CPU) — differential
  **2493 cases, 2318 pass / 175 fail**, baseline diff FULL
  (2493/2493, no regression); negative 390/390; re-pin guard armed
  in worktree-vs-HEAD mode, **0 PASS→non-PASS flips** (the four new
  rows are born FAIL/frontend-export — no Cases-line obligation, but
  they ride BUG-070/071's Cases lines as refusal pins); bug-index
  cross-check ok (incl. the new Pinned-by:none existence check);
  spec anchors 525+115 resolve; frontend pins green (deviation order
  pinned, twin wire byte-identical, sha 1851de59aa76…); frontend
  unit tests + eval tests (141) ok; core build warning-free. The
  set-diff vs 56ebcde9's record is exactly the four new
  FAIL/frontend-export rows.

## 2. A-2 — flip-taxonomy correction [AGENT]

1a084fe5's message states "PASS->non-PASS flips: NONE." That was a
TAXONOMY error, not a data error: the re-pin REMOVED the PASS row
`unsafe/boundary/sizeof-const`, and the re-pin guard's flip set is
"old-PASS ids absent from new-PASS" — a removed PASS row IS a
PASS→non-PASS flip (flip by row-removal). The correct statement:
**1 flip, by row-removal, on BUG-070's Cases: line** (which is why
the guard passed). Confirmed mechanically by the A-4 exercise (§5):
the guard at 1a084fe5 reports "1 PASS→non-PASS flip(s), all listed
in BUGS.md Cases". Since the audit fix round the removed id lives in
BUG-070's PROSE, not its Cases line (check-bugs now requires Cases
ids to name live rows); the removal record is unchanged in substance.

## 3. Commit-message errata (messages are history; corrections live here, not in amended commits)

- (e1) 1a084fe5: "NEW RED-BY-DESIGN (7)" — the list that follows it
  names EIGHT rows (panicky-between, init/hidden-dep-refused,
  layout-ops sizeof-fixed + layout-struct, dyn-boxed, shim-value
  shimmed-value + unmodeled-value, repeat-bound-refused). The count
  is wrong; the list is right.
- (e2) 56ebcde9: "the E8 fileOrder record addition (nine jq -S
  lines)" — the structural diff is EIGHT lines (re-verified at the
  fix round: `diff gs-main.s.json gs-branch.s.json` = 8 added lines).
  The delta class (fileOrder-only) is unaffected.
- (e3) ca46f8ac describes the resumed lane's tip gate coming back
  "RED four ways"; the red-run log itself DID NOT SURVIVE the crashed
  worker (nothing under artifacts/ or .tmp/ carries it). The four red
  causes are reconstructable from ca46f8ac's fixes and were
  independently confirmed by the A-4 exercise (§5: plain ci at
  1a084fe5 fails bug-index cross-check + spec-anchor citations, the
  two static legs of that red), but the differential legs of that red
  run have no surviving primary record.

## 4. fileOrder consumer — resolution [AGENT, per the audit fix brief]

The wire's `fileOrder` program key (T1 item 3, dc122857) records the
realized E8 member but currently has NO decoder-side consumer: the
lowering ignores unknown program keys. Resolution: **the T3 strict
decoder becomes fileOrder's consumer at merge** (its
unknown-key-refusing schema must enumerate fileOrder, which makes the
record load-bearing); **until then the twin-wire byte pin is the
guard** — any drift in the recorded order moves the pinned bytes and
scripts/check-frontend-pins fails.

Related attestation, same pin: under A6 the raft twin's EVALUATION
ORDER moved at four sites (the sweep-scoped ordered-event hoist
reorders len/cap/min-max evaluation relative to neighboring calls at
four places in the subject tree) [AUDITOR finding, fix-round brief].
The move is deliberate (BUG-062's fix realizing the spec-forced
call-order point) and is attested by the twin-wire byte pin's
recorded move at 1a084fe5 (reason in that message) — the pin is
exactly the mechanism that keeps such moves visible and deliberate.

## 5. A-4 — the re-pin guard, exercised once [AGENT]

Procedure (2026-09-01): throwaway worktree at 1a084fe5 (build state
hardlink-copied; Lean sources identical to 56ebcde9's), plain
`GOLEAN_ALLOW_NO_DIFF=1 scripts/capped scripts/ci` — the flip-guard
step runs regardless of the differential-record allowance. Result:

- The guard **ARMED** in HEAD-vs-HEAD~1 mode (1a084fe5 changed
  baselines/native-full.tsv relative to 4239697e) and **PASSED**:
  `ok re-pin guard (1 PASS→non-PASS flip(s), all listed in BUGS.md
  Cases)` — the one flip is the sizeof-const row-removal (§2), found
  on BUG-070's Cases line as it stood at that commit.
- Overall ci at that historical tip: FAIL on bug-index cross-check +
  spec-anchor citations — the two static reds of the gate-red round
  ca46f8ac fixed; expected, and consistent with the branch record.
- The throwaway worktree was removed after the run; the ci log
  survives (gitignored) at `.tmp/fixround/a4-guard-ci.log` in this
  lane's worktree.

## 6. Audit fix round — per-finding summary (2026-09-01, this commit)

1. **BLOCKER-1** (walkFormatterBoxing completeness, fmtdesugar.go):
   `=`-form range key/value targets + expression-switch case
   comparisons added to the enumerated boxing-context list;
   implementor scan DECOUPLED from the boxing walk (implementor in
   any unit arms the walk over every unit); type-parameter-typed
   boxing inside a generic body is a conservative HIT. Probes: fm1,
   fm4, fm7, fm8 all REFUSE at this tip (were silent wrong answers);
   fm2/fm3/fm5/fm6 still refuse; formatter-dyn-hole still refuses;
   fmt/v-composites exports (16 sibling rows stay PASS). Three new
   refusal fixtures pin the wrong-answer shapes (formatter-box-*).
2. **BLOCKER-2**: BUG-071's Status/closing paragraph rewritten for
   the boxing-reachability key — ENUMERATIVE character and the named
   extension point (the context list in checkFormatterDynHole's
   header) stated; same correction in formatter-dyn-hole's fixture
   header. The false "never a wrong answer" claim is replaced by the
   honest statement that a missing context IS a reopened
   wrong-answer channel (with the audit's four shapes named).
3. **E7 transitivity** (hiddendep.go): methodReadsInitVar is now
   transitive over statically-resolved calls (same worklist
   discipline as the reach walk); the ":40 header" no longer claims
   sound over-approximation for the shipped direct-read gate — the
   scope and the shared func-value residual are stated. Probes: e7d
   (helper-indirection perturbation) REFUSES; e7b REFUSES; e7a still
   refuses; e7c (func-value channel) still lowers — the recorded
   residual; the pinned deviation case still lowers under the allow
   (check-frontend-pins green).
4. **unsafe dot-import** (emit.go checkUnsafeLayoutOps): `import .
   "unsafe"` refused outright before the selector walk (probe u2 —
   Sizeof as a bare identifier walked past the pre-fix scan); header
   comment corrected (aliased imports are caught by resolution;
   dot-imports were the escape). New refusal fixture
   unsafe/dot-import/sizeof-bare.
5. **E7 warning surfacing** (scripts/diff-coverage, both export
   sites): frontend stderr on a SUCCESSFUL export now prints to the
   gate's stderr — the E7 allow's WARNING is no longer swallowed.
6. **A6/E13 census**: §E13 gains the min/max evidence table (probes
   a6p/a6q, gc @ go1.26.5 vs machine re-run at this tip) + the
   [AGENT] membership sentence (min/max join the E12/E13 ANF
   call-first family; assert-axis divergences census'd, no pin);
   language-coverage-ledger:Order_of_evaluation gains the qualifier
   (divergences census'd under E13, not open bugs);
   Min_and_max row notes the realization point.
7. **Record honesty batch**: this file; B-3 wording fixed at its four
   sites (BUG-032 A6 amendment, BUG-062 Status, inventory §E6,
   baseline header + len-vs-call-order/cases.tsv) — A6 is NOT a pure
   narrowing: receive-free functions gained the panicky-composition
   refusal while BUG-062's silent wrong answer died there, trade
   stated; inventory's stale E8 backlog line corrected (file-list
   mode, not non-go-command build systems); trimspace-repeat's
   mechanism name corrected (goleanShimStringsRepeatBound);
   check-bugs [TRUST-ADJACENT] now verifies Cases-id EXISTENCE for
   Pinned-by:none entries (the dangling sizeof-const id is resolved:
   removal named in BUG-070's prose, Cases line carries live rows
   only).
8. **A-4**: §5 above.
9. **NOTE-10**: non-constant shift counts added to
   sweepPanickyInlineBefore's census (the "mirrors
   initializerEffectIsolated" claim was false — that census has had
   SHL/SHR since A6); probe a6s: s1 (len, shift-left, ordered call
   after) now refuses fail-closed; s2 (min) hoists call-first per
   E13, gc-agreeing on the probe (gc realizes the arg's index panic
   on both, re-probed at go1.26.5).
