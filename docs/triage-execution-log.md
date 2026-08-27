# Triage-execution log — the landing branch (2026-08-27)

Executor: [AGENT] Fable, w1-prover worktree, branch `triage-landing`
(created at `20cda772`, the w1-prover wave tip, per the plan's
mechanism — deletions stay legible as commits on a working branch).
Spec: the [USER]-approved `docs/2026-08-27_triage-plan.md` (in the
design-pass worktree at approval time) + the [USER]-approved decision
set + the adversarial pre-execution check's mandatory amendments
A1–A8. Archive ref `archive/callspec-era` = `20cda772` (pre-existing;
verified before the first deletion — every deleted line is
recoverable).

**The approved decision set** ([USER], at sign-off): (1) ZERO
CallSpec members survive as witnesses; (2) `Invariant.lean` is
ARCHIVED, not landed; (3) the Surface FnSpec designated family
stays; the fork/join pinned-stream rows reclassify to non-designated
witnesses; (4) the W2Gate demo gap is accepted; LangC/D keep per the
plan's consumer evidence; (5) full ceremony.

## Per-slice commits (each left the tree buildable; focused capped
builds between slices, every build judged by captured exit code)

| slice | commit | content | build |
|---|---|---|---|
| 1 | `3ed23de9` | LAND-prep: `Frame/PlugWitness.lean` (A4) + `Sym/CrossingWitness.lean` (A5) + `Audit/Landing.lean` pins + A1 (Audit/W1 imports ReflectConc directly) — witnesses land BEFORE the kills | EXIT=0, 74 jobs |
| 2 | `1fcde452` | K-1a/b/c/d: SpecJudgment + 6 member modules + pilot/gate chain + fixture mass + `tools/relayout/CBfLitGen.lean` (23 files); MapOrderSpecs→MapPerm salvage (unitV/idKV + idKV_keys/filter + idsFam_population/lookup_agree/sorted_collapse) in the same commit; root + Audit/W1 + Audit/W2 prunes; A7 riders (MapPerm header/:757, mapPickLoop_perm SCAFFOLD label, ReflectConc consumer note, Crossing header + applyStrict_deref SCAFFOLD, PlugProbe relabel, Plug.lean:9/40) | warm EXIT=0 (72), full EXIT=0 (525 jobs) |
| 3 | `b09a545f` | A6: `Invariant.lean` DELETED (archived, [USER] decision 2); importer grep re-run pre-deletion — root aggregator only; F-6 pin candidate `I.abs_oneLeaderPerTerm` dropped | EXIT=0, 484 jobs |
| 4 | `9f309306` | K-2 `Frame/Relocate.lean` + K-3 `Frame/ChoiceInv.lean`, with A2 (Kit.lean import line + span_relocate pin pair) and A3 (Audit/ChoiceInv import + two pins; ChoiceCanon pins stay) riding the same commit; InitSpec:14 A7 rider | EXIT=0, 484 jobs |
| 5 | `204e30cb` | TRUST-ADJACENT, own commit: designation reclassification — the five fork/join pinned-stream rows out of Challenge/Solution/Audit-designated-list/judge-config together (56 → 51 designated); proofs stay in `GoldenForkJoin.lean` with pins. Includes the amend that removed a `[USER]` bracket from the in-list comment after noticing the judge wrapper's sed list-parser ends at the first `]` — an executor-caught parser hazard, recorded here | EXIT=0, 525/521 jobs |
| 6 | `ea0c91a3` | Hygiene: K-5 stale-docstring batch (11 files verified stale — dead `DriverNetWitness`/`LensInst`/`RoundMaLemma`/`ChoiceCanonWitness`/`Sym/UtoaSpan` citations, the false NativeObligations "nothing consumed" claim), K-4 dispositions (DriverNet invariants = span-lemma parameters; AbsStateV2 `_ren` keep-note), K-6 doc landings (`2026-08-16_symbolic-domain-design.md` from wp-design @ c3dc3986 — closes the wp-design lane per P-4; `2026-08-25_campaign-layerc-design.md` from raft-proof-campaign), 10 `artifacts/probe/*` citations marked "(untracked scratch)", L-9 supersession banners (w1-judgment-design, m-mechanism note), L-5 G-REPR note on AbsTwinCheckerRead, ARCHIVE.md CallSpec-era section, mechanism-registry triage addendum | EXIT=0, 522 jobs |
| 7 | `5921c757` | F-6 pin wave in `Audit/Landing.lean`: MapPerm (incl. scaffold-labeled `mapPickLoop_perm` + the salvaged idsFam trio), Crossing representatives, reader mini-witnesses, ghost-acks; Invariant pins dropped (A6). Axiom lines taken from the compiler's own output (first-run mismatches corrected) | EXIT=0, 521 jobs |
| 8 | `c2e1824d` | Gate-fix: `scripts/ci`'s import-direction lint FAILED on MapPerm.lean:3 (the plan's recorded L-3 altitude smell — the full gate had never run on this branch's waves). [AGENT]: honor the lint, no exception — `mapPairs_perm`/`mapPairsD_perm` moved VERBATIM to the new target-side `Specs/Raft/MapPermRead.lean` (namespace kept). No statement/proof changed | EXIT=0, 523 jobs |

## The amendment discharge table

| amendment | status | how |
|---|---|---|
| A1 | DONE (slice 1) | `import GoLeanProofs.Sym.ReflectConc` added to `proofs/Audit/W1.lean`; its retraction pins survive the pilot chain's death (verified by the slice-2+ builds) |
| A2 | DONE (slice 4) | `Audit/Kit.lean`'s `import GoLeanProofs.Frame.Relocate` deleted in the same commit as `Frame/Relocate.lean` + the `span_relocate` pin pair (tombstone comment in place) |
| A3 | DONE (slice 4) | `Audit/ChoiceInv.lean:2` import deleted with `Frame/ChoiceInv.lean`; the two ChoiceInv pins pruned; the ChoiceCanon pins at :31-41 survive |
| A4 | DONE (slices 1+2) | `Frame/PlugWitness.lean`: `callSpan_plug_witness` + `stepFn_plug_witness` — named, pinned (`Audit/Landing.lean`), judgment-free, APPLYING `callSpan_plug` and `stepFn_plug` on the probe program at OPEN caller context under the rule's own premises (∃-side canonical run + non-wrapper fact discharged by kernel evaluation, the charter's carve-out). Cited from Audit/W2's plug-pin section docstring. PlugProbe header relabeled honest (concrete probe, NOT a witness; G-BIND retirement condition). NOTE: witnesses landed one commit BEFORE the W2Gate deletion (slice 1 vs slice 2) per the mission's execution order — at no commit is the family witness-less, which is the amendment's intent |
| A5 | DONE (slices 1+2) | `Sym/CrossingWitness.lean`: three named span-derivation witnesses over abstract states/symbolic lengths — lenNeg (normalize collapse via `normalize_int_eq`/`int_ofNat_cast` + the length read via `applyStrict_length_slice`, whose engine is `validateSlice_ok`), ifSplit (`stepFn_ifK_true` as a span prefix), read (`loadLoc_base` → `applyStrict_indexGet_slice`). Crossing.lean:28-33 rewritten to cite them. Scaffold trio disposition [AGENT]: `applyStrict_deref` SCAFFOLD-labeled (G-REPR/G-CALLS resume); `loadLoc_base` now HAS a live consumer (witness 3) — labeled with its consumer instead; `int_ofNat_not_neg` had in-module consumers all along (applyStrict_indexGet_slice's range checks) — the amendment's zero-consumer premise was wrong for this one name, corrected on the record rather than mislabeled |
| A6 | DONE (slice 3) | Importer grep BEFORE deletion: `Specs/RaftPilot/Invariant.lean`'s only importer = the root aggregator (recorded above) — nothing on the LAND list imports it; deleted whole; F-6 pin candidate dropped; readers (AbsTwinCheckerRead + RenCongr delta) landed with their pins |
| A7 | DONE (slices 2/4/6) | ReflectConc:21, MapPerm:44/:757, InitSpec:14 (ChoiceInv.anchorRunProg cite), the K-5 ~12-file batch, hlogBridge went with the Invariant module (A6); no LAND file's statement mentions CallSpecR (grep: prose-only mentions remained and were reworded — MapOrderSpecs' salvaged lemmas were already CallSpec-free in statement) |
| A8 | DONE | No in-tree docstring cited WordFreq/Count as mapPickLoop_generic's consumer (grep verified); the correct citation (`Examples/WordCount/RangeGeneric.lean:481` is the real second consumer; WordFreq/Count is a re-derivation) is recorded in the mapPickLoop_perm scaffold label and here |

## STOP items

None. Nothing on the plan's LAND list turned out to import a KILL
item; the one unanticipated event (the import-direction lint firing
on the recorded altitude smell) was resolved INSIDE the plan's own
recorded disposition (the L-3 note said "revisit" — the lint forced
the revisit at landing; a placement-only fix, no statement changed,
recorded as slice 8) rather than by touching the gate.

## The gate ([AGENT] judged by captured exit codes)

- First run: `scripts/ci` → **RESULT: FAIL, exit 1**
  (`artifacts/triage/gate-ci.log`): the single FAIL was the
  import-direction lint on MapPerm.lean:3 (above). All other steps
  green (core build warning-free 58 jobs; proofs+Audit 522 jobs;
  Challenge/Solution elaborate; eval tests 141 ok; surface purity,
  statement-TCB closure, golden/imported pins all ok).
- After slice 8: `scripts/ci` → **RESULT: PASS, exit 0**
  (`artifacts/triage/gate-ci-2.log`, 68 ok-steps, wall ≈4.5 min
  warm).
- **The no-diff hatch, used and disclosed**: this worktree has NO
  recorded differential run (`artifacts/coverage/` absent — the
  W1–W3 waves gated with proofs builds only). The branch touches
  ZERO runtime files (verified: `git diff 20cda772..HEAD` on
  `GoLean/`, `scripts/`, `baselines/`, `Corpus/` is empty; the only
  `tools/` change is the plan-mandated CBfLitGen deletion), so no
  differential is owed by the gate's own rule; `GOLEAN_ALLOW_NO_DIFF=1`
  was set per the documented hatch for environments that never
  record one, and ci printed its visible notes ("negative baseline
  diff NOT RUN (no record; explicitly allowed here)"; same for the
  differential). [AGENT] call, flagged here for the audit: the
  mission brief said "you are NOT a fresh lane"; the honest reading
  applied is that with zero runtime deltas the gate demands no
  differential, and fabricating a first-ever record from this lane
  mid-landing would prove nothing about this branch's changes. The
  post-merge `main` checkout retains its own recorded baseline.
- ci notes for the record: "comparator landmark OWED (scope): 4
  file(s) in Challenge's trusted closure changed" — the expected
  trigger; discharged by the judge run below.

## The judge

Owed thrice over (Audit.lean moved at W1 and W2; the designated-set
reclassification is trusted-closure movement). One landmark run at
the branch tip covers, per the widened 2026-08-22 trigger.

- First attempt: instant fail-closed refusal, exit 1 —
  "deps/comparator missing (scripts/comparator-setup)": this
  worktree had never bootstrapped the judge deps
  (`artifacts/triage/judge.log` first run). Remedy [AGENT], the
  documented offline worktree bootstrap, not a hack: `deps/comparator`
  copied bit-for-bit from the primary checkout's pristine tree; the
  wrapper itself then re-verified rev = the pin
  `fd2e25de155523dbce1f35d410511f9f63998461`, tree pristine,
  lean4export at its pin and built, landrun at its pinned modver —
  all fail-closed checks, none bypassed; the trust tool was not
  modified.
- `scripts/comparator-judge` at `c2e1824d`: **PASS, exit 0** —
  **51 theorems certified in 122 s**, fresh clone @ `c2e1824d7eb9`
  (`artifacts/triage/judge.log`; `judge-result.txt`: start
  21:22:02Z, end 21:52:58Z — total wall 30 m 56 s including the
  fresh-clone cold build of the Solution closure; the landrun
  sandbox reported swap peak 0B). The landmark marker
  `LANDMARK-RUN: c2e1824d7eb9 2026-08-27 51 122` was appended by
  the wrapper to `docs/2026-08-02_comparator-judge-sprint.md` and
  is committed with this record. NOT like-for-like with the prior
  56-theorem anchors — the designated set legitimately shrank by
  the five reclassified rows ([USER] decision 3); the run count 51
  equals the post-reclassification designated list exactly, which
  is the cross-check.

## Final counts (derivation-anchored: `git diff --stat`)

- vs the wave tip `20cda772`: 65 files, **+2,124/−29,792** (Lean
  only: 57 files, +824/−29,491 — the plan §6 predicted ≈28.4k KILL
  Lean; the extra ≈1k deletions are the Audit/root prunes, the
  Invariant module's 629, and the fork/join designated rows).
- vs `main` `84b5edb3` (what main will receive): 55 files,
  **+12,172/−388** — Lean +7,651/−382 across 42 files (plan §6
  predicted ≈+7,700/−260; the delta over the prediction is the two
  new witness modules ≈290 lines and the A2/A3 pin prunes on the
  main side), docs +4,521 across 12 files (five prover logs + three
  design notes with banners + the two K-6 doc landings + ARCHIVE +
  registry + this log).
- Designated set: 56 → **51** (the five fork/join pinned-stream
  rows; Challenge/Solution/Audit/judge-config moved together).
- Jobs: full proofs build 545 (wave tip) → **~523**.
- Modules: 24 Lean modules + 1 tool deleted; 4 Lean modules added
  (PlugWitness, CrossingWitness, MapPermRead, Audit/Landing).

## Trust-adjacent edits (FOR THE AUDIT)

1. Slice 5 (`204e30cb`): the designated-set reclassification —
   Challenge.lean, Solution.lean, Audit.lean designated list,
   judge-config.json ([USER] decision 3; judge landmark run covers).
2. Audit pin prunes riding the kills: Audit/W1 (13 SpecJudgment + 4
   pilot pins), Audit/W2 (4 W2Gate pins), Audit/Kit (span_relocate
   pair, A2), Audit/ChoiceInv (2 pins, A3) — each in the same commit
   as its subject's deletion, with tombstone comments.
3. Audit pin ADDITIONS: Audit/Landing.lean (slices 1+7).
4. The `]`-in-comment hazard fix inside Audit.lean's designated list
   (slice 5 amend) — comment-only, but IN the parsed region of a
   trusted file; the judge wrapper's parser now sees all 51 names
   (verified by re-running its own sed extraction).
5. No `GoLean/`, `scripts/`, or `baselines/` file was touched;
   no gate was edited; no baseline re-pinned.

## Honest deltas vs the plan (beyond the approved amendments)

1. **Slice 8 exists** (MapPermRead split) — plan called the smell
   "fix optional at landing"; the gate made it mandatory. Placement
   fix only.
2. **The witnesses landed one slice before the deletions** (mission
   execution order) rather than literally in the deletion commits
   (amendments' phrasing); intent (no witness-less state) preserved.
3. **`int_ofNat_not_neg`** was NOT scaffold-labeled (A5 named it
   zero-consumer; it has in-module consumers — verified, recorded).
4. **Invariant.lean** deleted whole per decision 2 — the plan's L-6
   (land minus two clauses) is superseded; ARCHIVE.md records the
   decision with [USER] provenance.
5. **The judge count changes** (56 → 51): the plan's §4 anchor
   ("designated list UNCHANGED by this landing") predates decision 3;
   the run at this tip is therefore NOT like-for-like with the
   742 s/56-theorem anchor — recorded as such.
6. Plan §6's proofs-tree line counts (279,724 → ≈287,160) don't
   reconcile with `find`-based counting in this tree (192,681 Lean
   lines post-landing under `proofs/`); my numbers above are from
   `git diff --stat` and `wc -l` at this tip — derivation stated,
   discrepancy noted rather than reconciled.

[AGENT] provenance throughout except where [USER] decisions are
explicitly cited.
