# Lane D — validation-apparatus audit (C4, apparatus side)

[AGENT] Lane-D worker report, 2026-08-31, branch `fidelity-assessment`.
Scope per the lane brief: the validation apparatus AS AN OBJECT — what a
green run certifies, guard coverage after the split, evidence
reproducibility, the fuzzing gap, statistical honesty per lane. Probes
run in this worktree (gitignored `artifacts/fidelity-probe/`); nothing
tracked modified except this report. All file:line refs are to this
worktree at commit 86180a5b.

## Summary

The exec-lane differential apparatus is unusually disciplined for a
research artifact: fail-closed on missing/unattributable records
(ci:563-604), atomic no-publish on infra death (diff-coverage:45-59,
G1-G4 fixtures test-lane-validation:176-256), manifest-sha attribution
that DOES cover cases.tsv expectations (coverage-manifest:720-731 —
expectations are IN the manifest, so a silent expectation edit trips the
fast gate's sha check), a mode-in-banner (ci:481-486), a per-class
untriaged ratchet with a set check (check-bugs.sh:186-264), byte-exact
frontend pins re-derived every gate (check-frontend-pins), and honest
per-lane epistemic captions recorded in the runner itself
(diff-coverage:350-370). The known-good properties the brief asked me to
verify rather than re-litigate all hold as documented.

The credible-outsider gaps are at the EDGES of that machine, not its
core: (1) the fast gate's replay judgment reads manifest_sha256 but not
the meta's own go_drift / git_dirty fields, and treats staleness as a
note, not a fail; (2) the negative lane has none of the exec lane's
attribution machinery (no meta, no manifest sha, no oracle-pin check, no
atomic publish); (3) two generated oracle artifacts
(Tests/FloatVectors.lean, tools/nativefrontend/inittask-std.tsv) are
tracked bytes no gate ever re-derives — my probes show both currently
byte-identical to fresh regeneration, and the check costs seconds; (4)
push/PR CI runs the fast gate only (GOLEAN_ALLOW_NO_DIFF=1), so a green
GitHub check on a runtime-code PR certifies build+units+pins, NOT the
corpus — documented in the workflow, easy for an outsider to misread;
(5) there is no fuzz lane at all, and the live fuzz capability is
`deps/grossmith` (the successor), not the frozen `side/gofuzz` the plan
names.

**C4 grade contribution (apparatus dimension): ADEQUATE** — the core
differential loop would survive hostile review; the negative lane,
generated-artifact guards, evidence convention, and corpus
representativity (fuzzing) would not, and each has a cheap-to-moderate
named fix below.

## Top 5

1. **D-4 — fast-gate replay certifies wider than it reads.** ci judges a
   cached latest.tsv by manifest sha only; meta's go_drift and git_dirty
   are recorded (diff-coverage:227-230) but never consumed; HEAD
   staleness is an ok-line suffix, not a fail; dirty-tree edits produce
   no staleness signal at all. REOPEN, S.
2. **D-5 — negative lane lacks the exec lane's integrity kit.** No meta,
   no sha attribution, no oracle-pin check, non-atomic publish
   (coverage-negative:20-40). 390 rows of the C1/static-claim evidence
   ride on it. REOPEN, S/M.
3. **D-6 — generated oracle artifacts have no re-derivation gate.**
   FloatVectors (33,004 hardware-oracle vectors) and inittask-std.tsv
   (362 gc-derived rows) are consumed as tracked bytes; a value edit is
   invisible to every gate. Probed: both regenerate byte-identically at
   the pin in seconds. REOPEN, S.
4. **D-8 — no fuzz lane; the revival target is grossmith, not gofuzz.**
   The prototype is frozen (LESSONS.md freeze record) and its GoLean
   adapter is interface-dead (7-field vs 10-field manifest, stage-vocab
   drift); `deps/grossmith` produced BUG-042, the BUG-062 widening, and
   two genuine gc bugs across ~880k generated programs. Missing pieces
   for a sound lane: dedup, shrinking, automated corpus promotion, and a
   manifest/stage contract test. REOPEN, M (phase-3 work program item).
5. **D-2 — push/PR CI green ≠ corpus green.** The differential runs only
   nightly/dispatch; the per-commit corpus check is a local convention
   (`--diff` for runtime changes), not a mechanical gate. Documented
   honestly in ci:20-23 and the workflow; flag it in any external claim
   of "CI-verified". KEEP with a mandatory scope caption.

---

## 1. What a green run certifies (the table)

Verified against scripts/ci (707 lines), scripts/diff-coverage (1368),
scripts/coverage-baseline-diff (73), scripts/coverage-negative (124),
the certified-slow mechanism (diff-coverage:1114-1190, 574-674;
baselines/certified/ — currently ONE record,
imported-goose__channel__google-search, matching the one tier=slow
manifest row), and the workflow (.github/workflows/lean_action_ci.yml).

| Step | `ci` (fast) | `ci --diff` | `ci --slow` |
|---|---|---|---|
| Escape-hatch scans (3 layers), engine-isolation lint | re-executed | re-executed | re-executed |
| Oracle toolchain pin vs baselines/go-oracle-pin | re-executed (ci:166-183; absent go = note, mismatch = FAIL) | re-executed twice (ci + diff-coverage:147-170, which REFUSES) | same |
| check-bugs / check-coverage / spec-anchors / lane self-test (fast half) / imported-goose verbatim | re-executed (static; read the TRACKED baseline, not fresh runs) | re-executed | re-executed |
| Core build + GoLean-warning watch | re-executed | re-executed | re-executed |
| Frontend pins (deviation observation + twin wire) | re-executed end-to-end: fresh frontend emit + fresh machine run vs pinned bytes (check-frontend-pins:42-80) | same | same |
| Frontend unit tests, eval tests (incl. FloatVectors sweep) | re-executed — but against TRACKED expectation bytes (see D-6) | same | same |
| Exec differential: go oracle, frontend emit, machine runs | **replayed**: artifacts/coverage/latest.tsv judged vs baseline | re-executed per case (fresh `go run`, fresh `go run ./tools/nativefrontend` emit, fresh golean runs) | same |
| tier=slow membership/confluent envelope enumeration | (inside the replayed record) | **replayed from baselines/certified/** — visible CERTIFIED-CACHED; fresh wire-sha + params checks + 4 fresh driver-coupling runs + fresh go samples (diff-coverage:1114-1139, 1211-1243) | re-executed and DIFFED against the tracked record; mismatch fails loud (diff-coverage:1172-1190, 648-664) |
| Negative corpus (390 rows) | **replayed**: negative-latest.tsv diffed `--full` vs baseline (ci:521-537) | re-executed (`go build` per case, ci:513-520) | same |
| Baseline re-pin guards (both baselines) | re-executed (worktree-vs-HEAD or HEAD-vs-HEAD~1; ci:607-699) | same | same |

Known-good properties verified holding, not re-litigated: no-record =
FAIL not skip (ci:590-604, negative twin ci:529-536); meta-less or
sha-mismatched record = FAIL (ci:563-575); mode in the banner
(ci:481-486); infra death publishes nothing (diff-coverage:45-59,
241-259, exercised by G1-G4); unknown ci flag = refusal (ci:67-81);
worker death fails closed per-row (diff-coverage:1331-1342); baseline
duplicate rows flagged (coverage-baseline-diff:44-50); typo'd
Status/Pinned-by fail closed (check-bugs.sh:53-65).

**Where a stale/cached artifact can look fresher than it is:**

- **(a) Corpus source bytes** (exec lane). The manifest sha covers
  cases.tsv EXPECTATIONS (id/args/status/reason/lane/params —
  coverage-manifest:720-731) but not main.go bytes; ci's own comment
  records this (ci:556-560). Weight, assessed: the exposure is (i) a
  local uncommitted edit — no signal at all, since the staleness note
  compares run-commit vs HEAD only (ci:543-546); (ii) a committed edit
  without `--diff` — visible only as a ` [stale]` suffix on an OK line
  (ci:579), and bounded by the nightly `--slow` (workflow cron, line
  ~31), i.e. ≤1 day for pushed work. So the recorded limit is real but
  cadence-bounded for anything that reaches the remote; the unbounded
  window is purely local. See D-1/D-4.
- **(b) The negative lane entirely** — no meta at all (D-5): the fast
  gate cannot even ask whether negative-latest.tsv is attributable.
- **(c) go_drift / git_dirty recorded but unread** (D-4): a record
  produced under GOLEAN_ALLOW_GO_DRIFT=1 (meta rows go_toolchain /
  go_drift, diff-coverage:227-230, added exactly so this would be
  distinguishable) is judged by the fast gate as a full certification —
  no consumer reads those fields (grep: only diff-coverage writes them).
- **(d) tier=slow envelope content** — machine-side envelope drift on
  the cached path is deferred to `--slow` by design and SAYS so
  (CERTIFIED-CACHED detail, diff-coverage:1281-1283). Honest; the only
  note is that the cadence claim lives in the nightly cron, nowhere
  gated.

### Findings

**D-1 (fast-gate scope caption). KEEP** — the fast gate's replay-only
nature is documented at ci:20-23 and surfaced per-run (partial notes,
stale suffix, FULL/PARTIAL wording). The one wording hazard: `ok
baseline diff FULL (2478/2478, no regression) [stale]` is still an `ok`
line; an operator scanning for FAIL sees green. Covered by D-4's fix.

**D-2 (push/PR CI runs no differential). KEEP + caption.** Workflow
lines 172-197: fast gate with GOLEAN_ALLOW_NO_DIFF=1; full corpus only
on schedule/dispatch (lines 199-222). This is a deliberate, commented
design and the nightly is `--slow` (strongest form). But any external
statement of the form "CI-green" must carry the caption that per-commit
CI certifies build+units+pins+static cross-checks only; the corpus
certification cadence is nightly. C4 impact: an outsider reading the
badge will assume more than ran. Recommendation: KEEP the design; add
the caption to README/claims documents (not to the gate).

**D-3 (GOLEAN_ALLOW_NO_DIFF in a local env). KEEP** — it produces a
visible RESULTS note ("baseline diff NOT RUN … explicitly allowed",
ci:598-600), never a silent skip. Speedbump-adequate.

**D-4 (replay judge ignores its own attribution fields). REOPEN, S.**
The meta was extended (delta-review DR1 MEDIUM-3, diff-coverage:226-230)
precisely so a drift-probe run "must not be indistinguishable from an
oracle-of-record run in the artifact a re-pin consumes" — but the fast
gate's judge (ci:563-575) reads only manifest_sha256. Work: in the
meta_ok block, (i) FAIL (or at minimum non-ok note) on `go_drift 1`;
(ii) note `git_dirty true`; (iii) consider demoting a `[stale]` full
certification from `ok` to a note-line. Size S — a few lines in the
existing block. Not adversarial hardening: it closes a fail-open path
the meta already exists to prevent.

**D-5 (negative-lane attribution asymmetry). REOPEN, S/M.** scripts/
coverage-negative has: no oracle-pin check of its own (only `command -v
go`, lines 20-23 — the pin holds only when invoked under ci, whose step
0c ran first; a standalone run against a drifted toolchain records
silently), no meta/sha/commit attribution, results written directly and
incrementally to negative-latest.tsv (line 40; a killed run leaves a
readable truncated file — caught only because ci diffs it `--full`, so
missing ids fail), and no staleness note in ci's negative branch
(ci:521-537). An edited negative case's expected_substring or source is
re-validated only by a fresh run, with no sha to notice the edit against
the cached record — strictly weaker than the exec lane's recorded
limit, and unrecorded. C4 impact: the 390-row compile-rejection
guardrail (the static-semantics evidence lane B leans on) is the least
attributable artifact in the chain. Work: port the exec lane's pattern
(up-front rm, pin check, tmp+mv publish, meta with manifest sha; teach
ci's negative branch the same meta_ok check). Mostly copy-paste; M only
if the negative manifest needs a sha convention of its own.

## 2. Guard coverage map (post-split)

Tracked artifacts that influence semantics claims, and what watches
them:

| Artifact | Guard | Verdict |
|---|---|---|
| cases.tsv expectations (all 2478 rows) | manifest sha in meta, checked by fast gate (ci:568-575); lane/param shape by coverage-manifest + harness re-validation + test-lane-validation fixtures | **guarded** (contra the brief's worry — expectations are inside the manifest) |
| Corpus main.go bytes | fresh `--diff` only; recorded limit ci:556-560 | cadence-bounded gap (D-1/D-4) |
| baselines/native-full.tsv, negative-full.tsv | re-pin guard (flip laundering, ci:607-699) + check-bugs cross-check + duplicate check | guarded |
| baselines/pins/* (deviation + twin wire) | check-frontend-pins, byte-exact, every gate — the split-audit restoration the brief cites | guarded |
| baselines/certified/* | wire-sha + params on every --diff; content re-derived nightly --slow | guarded (cadence-deferred, visibly) |
| baselines/go-oracle-pin | live-toolchain equality in ci + diff-coverage + workflow pin; moves are convention-guarded ("full run + written reason") | guarded (move discipline is convention, acceptable speedbump) |
| baselines/untriaged-count / -ids | check-bugs ratchet (per-class ceilings, set check, sum check) | guarded; ceiling RAISES are review-convention only, by design |
| Corpus/coverage/tags.tsv | manifest validation (unknown/dup tags) + check-coverage dead-tag FAIL | guarded |
| **Tests/FloatVectors.lean** | eval tests consume it; expectedCount check is SELF-REFERENTIAL (count recorded in the same generated file, GoCoreEval.lean:2021-2038 — catches truncation, not edits) | **unguarded (D-6)** |
| **tools/nativefrontend/inittask-std.tsv** | embedded via go:embed (inittask.go:63); frontend refuses ABSENT rows (fail closed) but an EDITED row silently changes the realized init schedule; header's toolchain line is checked by nothing against the pin | **unguarded (D-6)** |
| Tests/GoCoreEval.lean expectations | hand-written test code; non-empty assertion D6-F3 (ci:465-470) | ordinary unit-test trust class — fine |
| imported-goose corpus bytes | check-imported-goose vs pinned upstream rev, every gate, fail-closed on missing checkout | guarded |
| raftsubject/ + tools/raftsubject twin assembly | twin-wire pin (frontend emit byte-exact) | guarded (frontend half; Lean consumer parked, stated) |
| **raftharness/** | nothing — no script references it (grep over scripts/ and .github/: zero hits) | **gate-orphaned (D-7)** |
| Frontend binary discipline | verified: every gate path compiles from source per run (`go run ./tools/nativefrontend` — diff-coverage:569,1083; check-frontend-pins:47,72); the only prebuilt-binary consumer is tools/raftsubject/runprobe.py (probe tooling, not a gate); no tracked ELF binaries (`git ls-files | file` sweep) | clean |

**D-6 (generated oracle artifacts unguarded). REOPEN, S.** Probes run
this session at the pinned toolchain (go1.26.5, matching
baselines/go-oracle-pin):

- `GO111MODULE=off go run ./tools/floatvectors` → byte-IDENTICAL to
  tracked Tests/FloatVectors.lean (33,004 vectors, seed 20260805).
- `scripts/gen-inittask-table -o <scratch>` → identical to tracked
  tools/nativefrontend/inittask-std.tsv modulo the `# generated:` date
  line (362 rows, 293 nodes).

So both artifacts are currently honest, regeneration is deterministic
and cheap (seconds), and the gap is purely that no gate performs the
comparison — a silent value edit (or a table left stale across a future
pin move — the header says "regenerate when the Go pin moves", and
nothing checks header-toolchain == go-oracle-pin) would pass every
gate. Work: a `cmp` step in ci (float vectors unconditionally; inittask
regeneration needs the toolchain, so gate it where go is present, with
the header-vs-pin equality as the cheap always-on half). This is
drift-protection in the existing check-imported-goose/check-frontend-
pins mold, not fortress-building.

**D-7 (raftharness/ gate-orphaned). REOPEN, S (or deliberate-park it).**
CLAUDE.md names `raftharness/` part of "the test suite for the
semantics", but post-split no gate builds, runs, or pins it (the twin
pin covers raftsubject + tools/raftsubject only). Either point a gate at
it or record it as parked-with-the-reasoning so the charter text and
the gate surface agree. C4 impact: minor — but a tracked artifact the
charter calls test suite, that nothing executes, is exactly what an
outside auditor grep-finds.

## 3. Evidence reproducibility (docs/evidence/, 132 files, 26 dirs)

Sampled 17 files across all four era groups (delegated sweep; findings
verified spot-wise). Verdict: **a strong, uniform de-facto convention —
entirely unwritten and unenforced.**

- 26/26 dirs have a README with the same title form; 24/26 carry a
  toolchain line (near-verbatim "Toolchain: go1.26.5 linux/amd64;
  GOCACHE repo-local; outputs verbatim"); 26/26 name the consuming doc
  (bidirectional citation); 24/26 have a Reproduction block.
- Best-in-class: 2026-08-12_scheduler-wedge-probes (commit ba6398ab,
  build command, run counts, Reproduction block) and 2026-08-21_
  w42-census (per-file "produced by" table, `git archive` reproduction,
  post-rebase byte re-verification).
- Gaps, ranked: (1) **commit SHA pinned in only 4/26 dirs** — cheap for
  the 21 gc-only dossier dirs (gc is the oracle; repo state irrelevant)
  but real for machine-tier records (the w32 dirs say "this tree,
  stage-C surgery applied" — unpinnable); (2) host identity never
  recorded beyond linux/amd64, despite explicitly load-dependent
  numbers (w32-postop's 60/200 vs 189/200); (3) generated-file headers
  carry dead absolute worktree paths (w42 sweep-pre.txt et al.); (4)
  2026-08-21_w32-qrow-probes records no command line at all; (5) no
  [AGENT]/[USER] provenance tags anywhere in the tree.
- Nothing in scripts/, AGENTS.md, or CLAUDE.md defines the convention;
  the only enforcement observed is retroactive audit (the w43 README
  exists because launch audit D7-evidence-F1 found it missing).

**D-9. REOPEN, S.** Write the convention down (one short section in
AGENTS.md or a docs/evidence/README: title form, toolchain line, commit
SHA for any machine-tier record, command lines, Reproduction block) and
backfill SHAs where recoverable. C4 impact: direct — "could a hostile
outsider re-run it?" is the CH2O-standard question, and today the
answer is "usually, by convention, unverifiably."

## 4. The fuzzing gap

State (delegated survey, key facts): `side/gofuzz` is **frozen, not
parked** (2026-08-05 maintainer decision; side/gofuzz/LESSONS.md:1-5,
131-161 — the assurance-work-self-selects post-mortem), lives outside
this repo's git entirely (gitignored `/side/`, primary checkout only),
and is superseded by **grossmith 2.0 at `deps/grossmith`**. The plan's
Lane-B line "the parked side/gofuzz project: state, why parked" should
be read against this: the revival object is grossmith.

What already exists vs what a sound fuzz lane needs:

| Component | Status |
|---|---|
| Generator | EXISTS and strong — invariant-carrying source synthesis, measured 100% compile/determinism/in-fragment at n=200 and held at ~877k scale (side/gofuzz/baselines/rates.tsv; LESSONS.md); grossmith 2.0 is the live successor |
| Oracle comparison | EXISTS but interface-dead: the adapter drives scripts/diff-coverage with a 7-field manifest (side/gofuzz/cmd/grossmith/main.go:1006-1034) against today's 10-field, fail-closed reader (diff-coverage:332-340), and its closed 12-stage vocabulary predates membership/confluent/racy. Every row would FAIL at stage manifest today |
| Infra-vs-finding discipline | EXISTS — exactly-once accounting + manifest-sha check + "infrastructure is never a finding" (side/gofuzz/internal/golean/golean.go:36-70,141-155); this is the model to keep |
| Dedup/triage | ABSENT (stage→class mapping only; differential rows were deliberately stop-and-ask) |
| Shrinking/minimization | DESIGNED, NEVER BUILT (tape-based design, side/gofuzz/PLAN.md §4.6; LESSONS.md:182) |
| No-regression / promotion | MANUAL ONLY — `scripts/fuzz-import` was never built (brief :226); findings entered Corpus/ by hand and it WORKED: BUG-042 (grossmith seed 559 → Corpus/coverage/exec/ints/defined-incdec, 11 pinned cases), BUG-062 widening (Corpus/.../builtins/min-max-vs-call-order), campaign 2's 79,800 judged programs → 5 non-matches, two of them genuine gc bugs (docs/2026-08-20_grossmith-findings-2.md) |
| Oracle-pin discipline | EXISTS repo-side and transfers as-is (go-oracle-pin + GOLEAN_ALLOW_GO_DRIFT pattern) |

**D-8. REOPEN, M** (phase-3 work-program item, not a gate edit now). A
sound lane = grossmith revival against HEAD + the 10-field/stage-vocab
adapter rewrite (small, well-localized — LESSONS.md:127-129 predicted
exactly this) + a CONTRACT TEST for the manifest arity and stage
vocabulary (the drift class already bit once, silently, in the frozen
prototype) + minimal dedup/shrink + a promotion path that lands findings
as cases.tsv rows so they enter the ratcheted baseline (the existing
manual practice, mechanized). The corpus-promotion end is the important
half for C4: a fuzz finding only becomes durable evidence when it
becomes a corpus row.

## 5. Statistical honesty (what a green encodes, per lane)

Populations (regenerated manifest): 2374 strict / 58 confluent / 25
membership / 21 racy = 2478; 1 tier=slow row. Membership sampling: 21
rows at default samples=5 (→ 5 plain + 5 `-race` go runs per gate,
diff-coverage:1056-1070), 4 rows at samples=1 (version-tracking mode).
Widths declared per row (2..300), author-asserted, mechanically checked
per consumption site since slice 4 (coverage-manifest:557-570).

Per-lane, verified against the runner (the in-script captions,
diff-coverage:350-370, match the mechanism — I checked the code against
its own caption):

- **strict** (96% of the corpus): ONE `go run` sample + machine
  equality + machine-side invariance over THREE fixed choice streams.
  Two structural limits, both honest but worth stating for C4: (i) the
  captions' own "structurally BLIND to scheduling"; (ii) the streams
  are 10/10/8 entries and `Choices.consume` yields the canonical 0 on
  exhaustion (State.lean:156-160), so the invariance sweep perturbs
  only the first ≤10 choice consumptions of a run — a program whose
  order-dependence first bites at the 11th map pick would pass strict
  invariance. The lane-classification guard (nondet tag ⇔ membership,
  coverage-manifest:515-541) is mechanical, but ASSIGNING the tag is
  authorial; the prefix-limited nondet sweep is the only mechanical
  misclassification detector. Confidence encoded: "equal to gc once,
  under the pinned toolchain, on this box, with no detected
  order-sensitivity in a shallow choice prefix."
- **membership**: every Go sample (plain AND -race, the schedule-
  perturbation source — probed 0/700 vs 6/6 orderings per the doctrine
  note) ∈ the machine's ENUMERATED set; enumeration is exhaustive over
  registry-point schedules within declared width/sites/cap/work/
  backedge bounds, fail-loud on every cap. ∀ on the machine side
  (within declared bounds), ∃-sampling on the Go side. Too-narrow has a
  loud alarm (sample ∉ set); too-wide has NO oracle — width metadata +
  the standing envelope-width review (membership-lane design note:138)
  police it, i.e. a human process, honestly labeled. members= pins
  cardinality where declared.
- **confluent**: |set|=1 certified over ALL schedules within bounds,
  then full strict differential on the singleton — the strongest lane;
  ∀-schedule on the machine side, one-go-run on the oracle side.
- **racy**: every enumerated path refuses (∀ within bounds) + one
  `-race` red sample; a green TSan sample FAILS the case into the
  three-way investigation (diff-coverage:475-478) — fail-closed in the
  right direction.

**D-10. KEEP** — the per-lane claims are stated where they're made, the
fail-loud cap discipline is real, and the residual softness (strict's
shallow-prefix invariance, membership's unpoliced upper edge, one-
sample oracles per gate for 96% of rows) is exactly what Lane B/C
should weigh as EVIDENCE-BASE limits, not apparatus dishonesty. One S
recommendation for the phase-3 report rather than the gate: the
strict-lane caption should state the prefix limit (streams ≤10 picks,
exhaustion→default) explicitly — today that fact lives only in
Choices.consume.

## Unanticipated (for the coordinator)

- The brief's worked worry "what stops a silent expectation edit in
  cases.tsv" has a better answer than expected: expectations are inside
  the manifest, so the sha attribution check catches them; only SOURCE
  bytes are outside it (§2 table, D-1).
- `side/gofuzz` is not recoverable-as-is and was never merely parked —
  frozen with a written post-mortem; the fuzz conversation should be
  about `deps/grossmith`, which found real bugs on both sides of the
  differential ("the oracle was wrong more often than the machine",
  grossmith-findings-2:22-23).
- Sandbox note for other lanes: /tmp is write-only in this environment;
  use repo-local gitignored scratch for probes.
