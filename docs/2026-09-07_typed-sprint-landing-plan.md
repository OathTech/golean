# Landing plan for branch `typed-consumer-sprint` (2026-09-07)

**Status: PLAN OF RECORD for landing the sprint's work; [AGENT] records
worker, lane `landing-plan-0907`, 2026-09-07. Nothing here is landed by
this document.** Every chunk below is built from the sprint tip by path
selection, gated on a clean tree, audited, and merged only on a separate
at-that-moment [USER] sign-off (`CLAUDE.md`, the merge protocol).

Subject: branch `typed-consumer-sprint`, tip `7edc298f`
(`7edc298f257519652646b7a59bca959671d33063`), 96 commits over main
`47195683`; 2,410 changed paths = 251 non-evidence + 2,159 under
`docs/evidence/`. The full path partition is Appendix A; the numbers in
this document are derived from `git diff --name-only
main...typed-consumer-sprint` and `git log main..typed-consumer-sprint --
<path>` at the time of writing (§6).

## 0. The ruling and the audit verdicts

**[USER] ruling (Mike, 2026-09-07, verbatim as relayed by the [AGENT]
coordinator — cite as relayed):** «The evidence blob should not land, and
generally we should not dump big evidence bundles on main (they can't be
easily hosted on GH for one). Can you make a plan to land this work
cleanly? We'll want to decompose and land in sane chunks that can be
reviewed. And where appropriate fix some of the issues, eg. the choice
tape stuff».

Two independent landing audits were read in full and are the source of
every finding id below (`A-Rn` = auditor A, `B-Rn` = auditor B). Both live
in the sprint worktree's scratch, `.claude/worktrees/typed-consumer-sprint/
.tmp/landing-review/{auditor-A,auditor-B}.md`; they are NOT tracked, and L6
copies them into `docs/` as the sprint's closing reviews (§2.6).

- **Auditor A (semantics / trust surface / gate integrity): DO-NOT-LAND
  the semantic and gate content as-is; one BLOCKER.** A-R1: the new
  `string-member` lane never compares gc's transported `messageBytes`
  against the modeled set — 5 of its 9 PASS rows are demonstrably
  divergent from gc at the pin (`invalid-{after,before}-lf`,
  `invalid-recovered` render a quoted `\xHH` form Go never prints;
  `equal`, `multiple`, `repanic-same-value-abort` print `[recovered]` where
  gc prints `[recovered, repanicked]`). A-R2 (HIGH): `renderPanicHead`
  bakes the collapse choice into evaluator recursion as one hard-coded
  member. A-R3 (HIGH): `renderStringMember` replaces a fail-closed `none`
  with an answer known to differ from gc. A-R4 (MED): `baselines/
  string-members/` has no re-pin guard. A-R5 (MED): no fresh full run at
  the tip; the last re-pin ran at 32 workers against a recorded limit of 2.
  A-R6 (MED): crash-channel authentication degrades silently to the raw
  fallback on the abort path. A-R7 (HIGH, process): the worktree is dirty
  (319 files, ~75.5k uncommitted insertions). A-R8–A-R12: LOW/INFO.
  Verified clean: `scripts/capped` byte-identical; frontend a pure
  addition (`wire.go`, `NativeToIR.lean` hash-identical to main — no 5a
  for `7edc298f`); twin pin unmoved; `scripts/ci` +94/−0, every new step
  can only add reds; the `diff-coverage` rework a net strengthening; the
  ~60 GoCore modules a genuinely additive proof layer; zero escape-hatch
  delta; the Iris customer outside the default build graph.
- **Auditor B (contract claims / records / evidence / landability):
  DO-NOT-LAND as one train step; SPLIT, and LAND-AFTER-FIXES.** B-R1
  (BLOCKER): the tip is not the artifact (272 staged + 47 unstaged + 15
  untracked files, including the trusted surface). B-R5 (BLOCKER): an
  uncommitted `AGENTS.md` hunk grants standing worktree-deletion approval.
  B-R7/R7a (BLOCKER): the evidence payload — 734,510 added lines in 2,159
  files, 114 MB, 36 `.tar.gz`, 345 exact copies of tracked files — is a
  duplicate of the repository, not an audit trail. B-R13 (BLOCKER): the
  staged `uintptr` repair overrides a standing latitude pin without citing
  it. B-R2/R3/R4/R6/R14–R17 HIGH; R8–R12, R18–R23 MED/LOW/INFO. Its F2/F3/F5
  answer table is reproduced verbatim in L6 (§2.6). Its landability
  partition (14 components, four branches) is the ancestor of the chunking
  below; deviations are disclosed where they occur.

## 1. Principles

1. **The committed tip `7edc298f` is the artifact.** The sprint worktree's
   dirty state is NOT landed: the staged `uintptr` workstream (the
   unresolved no-commit merge of `5f185fb3`, B-R1/B-R13 → L5), the
   uncommitted `scripts/ci` / `scripts/diff-coverage` / audit-tool /
   `docs/agent-sandbox.md` edits from the storage-maintenance overlay
   (§5), and the uncommitted `AGENTS.md` edit. **The `AGENTS.md` edit is
   rejected outright**: it adds "This is standing approval for routine
   retirement of finished, merged lanes" under a `[USER]` tag with no
   verbatim quote and no relay marker, three paragraphs below the file's
   own "Do not run `rm` … without explicit approval"; it contradicts the
   global instruction that "'Standing' or 'implied' permission … is
   completely forbidden" (B-R5, B-R19). It must not reach main on any
   branch in that form.
2. **The branch `typed-consumer-sprint` is retained, unmodified, as the
   archive of the sprint's full history and evidence payload**, indexed in
   `docs/ARCHIVE.md` (done in this lane). Nothing is rewritten; the
   payload stays reachable at `7edc298f` for anyone who needs the bytes.
   Snapshot ref `snapshot/typed-sprint-before-uintptr-20260906` also names
   `7edc298f` (per the pause-state record).
3. **One landing commit per chunk, built from the tip by path selection
   onto current main.** Each landing commit's message credits the sprint
   commits it carries BY SHA (the per-chunk lists are in Appendix A's
   `origin_commits` column and §2's "credits" lines) and states plainly:
   *"squashed from `typed-consumer-sprint`; the authored history is on that
   branch (docs/ARCHIVE.md)".* The squash is disclosed, never hidden.
   Hunk-split files (Appendix A, 11 of them: `scripts/ci`,
   `scripts/diff-coverage`, `lakefile.toml`, `GoLean/Interface.lean`,
   `Tests/InterfaceAudit.lean`, `scripts/check-interface{,.py}`,
   `baselines/native-full.tsv`, `docs/BUGS.md`,
   `docs/language-coverage-ledger.md`,
   `docs/2026-09-05_typed-contract-design-review.md`) are split by hunk
   along the chunk boundary; the worker records which hunks it took.
4. **Every chunk gets**: a design/records note under `docs/` (one file,
   named `2026-MM-DD_<chunk>-landing.md`, carrying the credits, the fixes
   applied by finding id, the exclusions, and the gate tail); a
   clean-tree gate (`scripts/capped scripts/ci --diff` at the chunk's tip,
   fresh — no cached certificates counted as fresh; `--slow` only if
   `wire.go`/`NativeToIR.lean` change, which no chunk here does — L5
   would); an audit ask (unconditional; scope/waiver the [USER]'s); a
   separate merge sign-off.
5. **Evidence per chunk = gate tails + small witness/probe files only**,
   each under the L2 size gate (§2.1), each in a `docs/evidence/<date>_
   <chunk>/` dir following `docs/evidence/README.md` (README, commands,
   toolchain line, commit SHA, host note). No archives, no source copies,
   no full-corpus TSVs (the pinned form is `baselines/native-full.tsv`;
   a full-run TSV is regenerable from the recorded commit). Everything
   not landed is inventoried once, in L6's `MANIFEST.tsv` (§2.6).
6. **No chunk weakens a gate, moves the oracle pin, or changes the trusted
   surface without saying so in its note's first section.** A chunk that
   cannot pass its gate on a clean tree does not land; it is re-cut.
7. **Order of landing is a dependency order, not a priority order**
   (§3): L2 → L1 → L4 → L3 → L6; L5 on ruling.

## 2. The chunks

### 2.0 How to read the partition

Appendix A lists every one of the 251 non-evidence paths with its chunk,
its hunk-split partners, and its origin commits. Counts (whole-file
assignment; hunk-split files counted once, in the chunk that lands first):

| chunk | paths | of which hunk-split (H) |
|---|---:|---:|
| L2 `land/gate-tooling` | 27 | 5 (`scripts/ci`, `scripts/diff-coverage`, `baselines/native-full.tsv`, `docs/BUGS.md`, `docs/language-coverage-ledger.md`) |
| L1 `land/typed-core-proofs` | 143 | 6 (`lakefile.toml`, `GoLean/Interface.lean`, `Tests/InterfaceAudit.lean`, `scripts/check-interface`, `scripts/check-interface.py`, `docs/2026-09-05_typed-contract-design-review.md`) |
| L1b (I1 declaration wire, a sub-chunk of L1 with its own gate) | 19 | 0 |
| L1-T (the recovery-TERMINAL slice — coupled to L3, see §2.2) | 7 (+1 spike file) | 0 |
| L3 `land/panic-text-tape` | 45 | (takes its hunks of the 11 H files) |
| L4 `land/observer-terminal` | 5 | (takes its hunks of `native-full.tsv`, `BUGS.md`, the ledger) |
| L5 `land/uintptr` | 0 at the tip (staged-only; branch `typed-uintptr-identity` @ `5f185fb3`) | — |
| L6 `land/sprint-records` | 5 | 0 |
| not landed: `docs/evidence/**` | 2,159 | — |
| unclassified | **0** | — |

Deviations from the brief's placement, disclosed: (i) `Corpus/controls/
string-members/**` is L3, not L4 — it originates in the string-member
commit `819182b5` and its only consumers are `tools/string_member.py:217`
and `tools/check_string_member_fixtures.py:32`; (ii) `Tests/
InterfaceContract.lean`'s whole delta is `+import Tests.PanicRendering`
(`ff7173dd`), so it is L3 and L1 carries NO delta to that file; (iii) the
committed `AGENTS.md` sprint-pointer hunk (`10fefeb3`) is L6, rewritten
(the sprint it points to as "active" is paused and being landed), not
"as-is"; (iv) L1 is split into L1 / L1b / L1-T because the dependency
check the brief required (§2.2) found real couplings.

### 2.1 L2 `land/gate-tooling` — FIRST

**Contents (27 paths + new files).** The whole `tools/coverageharness/`
delta (11 files: `abortkind.go`, `crashhook.go`, `crashview.go`,
`observe.go`, `split.go`, `main.go` and their tests, plus
`abortrecord_test.go` — the `--abort-record` mode it tests has no caller
until L3 and lands here as an unwired, unit-tested mode); the
`scripts/diff-coverage` rework MINUS the `string-member` lane hunks (the
lane-vocabulary line, the manifest constraint block, the
`tools/string_member_runner.py` dispatch block, and the `expected_reason
== "-"` exemption — all → L3); the three diagnostic oracle copies moved
onto the checked byte view (`scripts/cedar-census`, `scripts/gotest-triage`,
`scripts/membership-sampling`, commit `2b679404`) and the
`scripts/test-lane-validation` fake-oracle ack (`b5dd4076`); the two
Python gate scripts the new `scripts/ci` steps call
(`scripts/check-observer-controls.py`, `scripts/check-observer-tools.py`)
and their two `scripts/ci` steps ("observer byte transport", "diagnostic
observer transport and terminal classification"); the four observer design
notes (`docs/2026-09-06_observer-{crash-channel-design,
terminal-classification-design,classifier-repair,diagnostic-tools}.md`).
`lakefile.toml`: VERIFIED — the branch's +38 lines are ten new `lean_lib`
test targets and four globs added to `InterfaceTests`; `defaultTargets`
and the `GoLean` lib are unchanged; nothing in it is gate tooling, so
**L2 carries no `lakefile.toml` hunk** (they go with L1/L3).

**The corpus consequence L2 cannot avoid.** The new classifier refuses an
unauthenticated `fatal error:` that follows a `panic:` line
(`crashview.go`: `kind == "fatal" && (panics != 0 || fatals != 1)` →
"ambiguous fatal message/output before m.dying, refused"). So L2's own
full run flips `sync/mutex-unlock-fatal/during-panic-unwind` PASS →
FAIL/`go-observation`. The re-pin guard requires that id on a `- Cases:`
line, so **L2 carries the BUG-106 entry (`docs/BUGS.md`, hunk) and that one
baseline row flip plus its own measured header** (expected 3598 = 3352 /
246, but the numbers are whatever the run measures), and a ledger
movement paragraph of its own (post-vintage bucket +1) rather than the
branch's §8y text. Protocol satisfied exactly as the branch did it
(auditor A verified BUG-106's `Cases:` line at `docs/BUGS.md:6252`).

**NEW in L2 (the tooling lane implements; described here, not built
here):**

1. `scripts/check-evidence-size` — fail-closed, static, no build. Refuses
   (exit 1, naming each offending path and the rule it broke):
   - any tracked file under `docs/evidence/` larger than **256 KiB**
     (PROPOSED [AGENT]);
   - any `docs/evidence/<dir>/` whose tracked bytes exceed **4 MiB**
     (PROPOSED [AGENT]);
   - any tracked file under `docs/evidence/` with an archive extension
     (`.tar`, `.gz`, `.tgz`, `.zip`, and — [AGENT] addition — `.xz`,
     `.zst`, `.bz2`, `.7z`), regardless of size;
   - any tracked `docs/evidence/` blob whose git blob hash equals a tracked
     NON-evidence blob at HEAD (a source copy); the check is
     `git ls-files -s` hash equality, exact, not heuristic.
   - Grandfathering, fail-closed: main today already has 16 evidence files
     over 256 KiB (largest `docs/evidence/2026-09-04_c-arc-gu/
     expected-transformed-dump-sorted.tsv`, 6,205,426 B), one dir over
     4 MiB (`2026-09-04_c-arc-gu`, 10,410,369 B), zero archives, and one
     evidence↔source duplicate (`2026-09-05_iris-customer-review/
     Examples.lean.txt` = `spikes/iris-customer/GoLeanIris/Examples.lean`).
     The gate carries a tracked allowlist `docs/evidence/SIZE-ALLOWLIST.tsv`
     of `path\tsha256` for exactly those 17 + 1 entries; an allowlisted
     file that changes hash is refused (it may shrink only by leaving the
     list). No wildcard entries. The convention in `docs/evidence/README.md`
     (rule 4: "record the SHA — not copy the tree") becomes rule 9 with the
     caps and the archive/copy prohibition (B-R12).
   - Calibration against the sprint tip (`git ls-tree -r -l`): 140,641,636
     tracked evidence bytes, 93 files over 256 KiB, 36 archives, 229
     evidence blobs identical to non-evidence tracked blobs — every one a
     refusal.
   - Wired into `scripts/ci` as a `step`/`ok`/`bad` block in the static
     section (next to `check-bugs.sh`), never skippable by env knob.
2. A second static assertion, in `scripts/check-bugs.sh` or the new script
   (implementer's call, one place): no tracked file outside `docs/BUGS.md`
   contains a line matching `^## BUG-` (B-R17 — five whole-file ledger
   copies at the tip, one carrying a BUG-107 the ledger lacks).
3. `AGENTS.md`: one policy paragraph under a new "Evidence on main"
   heading quoting the ruling (§0, verbatim, relay-marked) and pointing at
   the gate and `docs/evidence/README.md` rule 9. `CLAUDE.md` "The gates":
   one sentence — the evidence-size gate is part of `scripts/ci`, bundles
   live on archive branches, quoting the ruling's first clause. These are
   L2's ONLY `CLAUDE.md`/`AGENTS.md` edits; the branch's `CLAUDE.md`
   retitle (B-R4) is not landed by anyone (§4 D6).

**Fixes applied in-chunk (by finding id).**
- **A-R6** — `crashEvidence.validate()` returns nil when ack AND report
  are both empty, so a missing hook registration silently falls through to
  the raw-marker fallback on the abort path (`ok`/`race` already require
  a non-empty ack — the asymmetry). Fix: on the abort path a crash-channel
  ack ABSENT → refuse by name ("crash evidence: no registration
  acknowledgement for an abort report") — never a silent fallback; the
  only exemption is a genuine pre-`main` abort (init-time panic before
  `_goleanSetupCrash()` runs), which must be identified positively by its
  trace shape and reported as its own cause, not inherited from the
  fallback. The design notes' "authenticate" claim then matches the code.
  Add the mutation to `scripts/check-observer-controls.py`.
- **A-R8** — `grep -aqF -- "$expected_reason"`: refuse (manifest stage) an
  `expected_reason` that is empty or contains a newline, in both
  `scripts/coverage-manifest` and the runner, so the latent
  conjunction→alternation relaxation cannot be reached.
- **A-R9, A-R10** — disclosed, not changed: the oracle program is now
  rewritten before compilation (`zz_golean_crash.go` injected,
  `_goleanSetupCrash();` spliced as `main`'s first statement, exit 78 as a
  setup sentinel) and `GOTRACEBACK=system` is added to the oracle
  environment. Both are recorded in the run manifest (`go_traceback`,
  `go_crash_channel`), both are changes to trusted surface #2's
  invocation, and L2's note says so in its first section (principle 6).
  Cosmetic: the `go_crash_channel` printf line is TAB-indented; fix.
- **B-R14** — the note carries a §7-style decision packet ("is the
  same-run crash channel + `GOTRACEBACK=system` + refusal of unauthenticated
  fatal-during-unwind an observation/terminal-policy change?") with the
  reproducer (`docs/BUGS.md` BUG-106's forgery counterexample), the affected
  claim (one row's PASS lost), the alternatives, and the cost of deferral.
  L2's merge sign-off IS the ratification (§4 D4); if refused, L2 is re-cut
  to `d0dbd469`'s byte-transport scope only and the classifier waits.
- **B-R12** — `docs/evidence/README.md` rule 9, above.

**Exclusions.** `tools/string_member*.py`, `tools/test_string_member.py`,
`tools/check_string_member_fixtures.py`, `scripts/check-string-members.py`,
the `string-member` lane hunks of `scripts/diff-coverage`,
`scripts/coverage-manifest`, `scripts/coverage-baseline-diff`, the
`scripts/ci` "explicit string-member apparatus" step (→ L3); the eight
Lean-proof `scripts/ci` steps (seven → L1, "recovery terminal" → L1-T) and
`scripts/check-declarations` (→ L1b);
the panic-controls / panic-markers corpus rows and their 20 baseline rows
and BUG-105 (→ L4); every `docs/evidence/` file except L2's own gate tails.
Note: `scripts/check-observer-controls.py` hashes
`Corpus/coverage/exec/panic-recover/panic-{controls,markers}/*` as a
source binding; until L4 those globs are empty and the hash list is
shorter — disclosed in L2's note; L4 restores them. The script's tested
behaviour (fake-oracle transport, exported shell functions, compiled
mutations) does not depend on the rows.

**Dependencies.** None (first). **Gate.** `scripts/capped scripts/ci
--diff`, fresh full run, on a clean tree, at the worker count of §4 D3;
`go test ./tools/coverageharness`. **Audit focus.** That every new step
can only add reds (auditor A's method: each is `step/if … ok else bad`);
A-R6's fix has no remaining silent path; the evidence gate refuses each
calibration class above and passes main + the allowlist; the diff-coverage
hunk split left no reference to `string_member_runner.py` or the
`string-member` lane; the one PASS→FAIL is on BUG-106's `Cases:` line.
**[USER] decisions needed.** D3 (workers), D4 (B-R14 ratification), D7
(the PROPOSED cap numbers). **Credits.** `d0dbd469`, `b5dd4076`,
`2b679404`, `819182b5` (harness parts only), `563c01de`, `a34bc969`,
`7774739a`, `96be72c9`, `838adc51`, `9726046c`, `a6df5cb3`, `313d1781`,
`639192b2`, `4bfeba58`, `99e0225d` (reviews).

### 2.2 L1 `land/typed-core-proofs`

**Contents (143 paths, whole files unless marked H).** All additive
`GoLean/GoCore/Boolean*.lean` (13) and `Recovery*.lean` modules EXCEPT the
two in L1-T; `GoLean/GoCore/AbortObservation.lean`, `RecoveryObservation`,
`RecoveryPoolObservation`, `RecoveryProgramObservation` (they import only
`Trace`/`ProgramTrace`/`RecoveryAdmission`/`RecoverySuccessfulRuns` — no
renderer); `GoLean/Interface.lean` (H: minus `import GoLean.GoCore.
StringPanic`, minus `import GoLean.GoCore.RecoveryPoolObservationTyped`,
minus the docstring section on the typed terminal classification); the
`Tests/` families `AbortObservation*`, `Boolean*` (7), `Recovery*` except
`RecoveryTerminal*` (11), `Tests/InterfaceAudit.lean` (H: minus `import
Tests.StringPanicMembers`, `import Tests.RecoveryTerminalAudit`, and the
`PanicText`/`StringPanic`/`StringPanicMembers`/`PanicRendering`/
`RecoveryTerminal*`/`RecoveryPoolObservationTyped` entries in its module
and export lists), the two fixtures `Tests/{boolean,recovery}-typing-
fixture/`; `lakefile.toml` (H: the eight test libs `BooleanTypingTests`,
`BooleanRuntimeTests`, `RecoveryTypingTests`, `RecoveryStorageTests`,
`RecoverySetupTests`, `RecoveryControlTests`, `AbortObservationTests`,
`DeclarationTests`[L1b] and the `InterfaceTests` globs `Tests.BooleanRuntime`,
`Tests.BooleanProgram` — NOT `RecoveryTerminalTests`, NOT
`Tests.PanicRendering`/`Tests.StringPanicMembers`); the seven `scripts/ci`
proof steps (Boolean typing, Boolean runtime, recovery typing, storage,
setup, control, abort observation — NOT "recovery terminal") and their
`scripts/check-*` scripts; `scripts/check-interface{,.py}` (H: minus the
`PanicText`/`StringPanic`/`PanicRendering`/`StringPanicMembers`/
`RecoveryTerminal*`/`RecoveryPoolObservationTyped` lines); the audit
tools `tools/{abort-observation,boolean-runtime,boolean-typing,
recovery-control,recovery-setup,recovery-storage,recovery-typing}-audit.py`,
`tools/check-{boolean,recovery}-typing-artifact.lean`,
`tools/check-recovery-fixture-controls.py`; `spikes/gate-a1/GateA1/
Audit.lean`; `spikes/iris-customer/**` (22 files) EXCEPT
`GoLeanIris/Terminal.lean` (→ L1-T; its line 44 states `"customer panic"
= stringPanicHead record.bytes record.recovered`) — the spike's `check`
and `GoLeanIris.lean` root must build without it, or the import is
dropped for L1; the 21 design notes `docs/2026-09-05_boolean-*`,
`docs/2026-09-06_{abort-observation-*,b7-context-store-design,boolean-*,
recovery-*(not terminal),shared-recovery-customer}.md`, and
`docs/2026-09-05_typed-contract-design-review.md` (H: `71183a62`,
`ce896516`, `d3ffb32b` hunks only; the `ff7173dd` corrigendum hunk → L3,
see B-R21).

**L1b — the I1 declaration wire (19 paths), a sub-chunk of L1 with its own
gate run and its own audit-ask line.** `tools/nativefrontend/
declaration.go` + two tests, `GoLean/GoCore/Declaration.lean`,
`GoLean/NativeDeclaration.lean`, `GoLean/StrictJsonParse.lean`,
`Tests/{DeclarationWire,StrictJsonParse,DeclarationAudit}.lean`,
`scripts/check-declarations`, `tools/check-declaration-wire.lean`,
`tools/declaration-audit.py`, `tools/lowerdiag/unclassified-formats.txt`
(+8 serializer formats, header note), `spikes/i1-declarations/`, the four
`docs/2026-09-06_i1-*.md`. It touches `tools/nativefrontend/` — trusted
surface #1 — ADDITIVELY (auditor A: no existing frontend file modified,
`declaration.go` has no non-test caller, emits a separate schema,
deterministic over 8 emits). It is kept inside L1 because the brief lists
`Declaration` there, but it lands only if its own gate shows `scripts/
check-frontend-pins` unchanged and the certified set byte-identical (no
executable wire byte can change). No 5a (`wire.go`, `NativeToIR.lean`
untouched).

**L1-T — the recovery-terminal slice (7 paths + 1 spike file): DETECTED
COUPLING, does NOT land in L1.** The brief asked for the dependency check;
here is its result. `GoLean/GoCore/RecoveryTerminal.lean` imports
`GoLean.GoCore.StringPanic` and states its main theorems over
`stringPanicHead` — `Inv.run_classified` (line 18: `.error (.panic
(stringPanicHead bytes recovered))`), `Inv.observed_abort_member` (52),
`runProgram_typed` (70), `runProgramPool_typed` (90), and
`runProgramPool_no_refusal` (100) rests on the renderer being total.
`stringPanicHead` is `PanicText.firstLine (renderStringMember bytes ++
" [recovered]" …)` — i.e. it is DEFINED over the L3 renderer, including
the baked `[recovered]` (A-R2) and the total `renderStringMember` (A-R3).
`RecoveryPoolObservationTyped.lean` (lines 12–54) likewise. Hence
`GoLean/GoCore/{RecoveryTerminal,RecoveryPoolObservationTyped}.lean`,
`Tests/RecoveryTerminal{,Audit}.lean`, `scripts/check-recovery-terminal`,
`tools/recovery-terminal-audit.py`, `docs/2026-09-06_recovery-terminal-
contract.md`, the `RecoveryTerminalTests` lib, the "recovery terminal"
`scripts/ci` step, the `Interface.lean` import/docstring, and
`spikes/iris-customer/GoLeanIris/Terminal.lean` are L1-T. Disposition:
**L1-T is restated over the unchanged machine and lands WITH or AFTER
L3**, not before. Restatement shape (for the L3 worker): classify the
terminal over the semantic abort RECORD (`abortRecord? c = some record`:
bytes, recovered flag, chain) and leave the rendered text to
`renderPanicHead`'s `Option`/choice contract (§2.3(b)); refusal-freedom
becomes conditional on the profile's admission excluding what the
renderer refuses (e.g. an admission rule that string-literal payload bytes
are valid UTF-8 — a checkable structural restriction, as charter §3.2
demands) or acquires an explicit premise. The customer facade sentence
about "typed terminal classification" is not landed until then.

**How to detect the coupling mechanically (the worker must run this).**
On a fresh worktree at current main: `git checkout typed-consumer-sprint
-- <every L1 path in Appendix A>` (whole files), apply the L1 hunks of the
six H files by hand, and `scripts/capped lake build GoLean.Interface
InterfaceTests AdmissionTests BooleanTypingTests BooleanRuntimeTests
RecoveryTypingTests RecoveryStorageTests RecoverySetupTests
RecoveryControlTests AbortObservationTests DeclarationTests` with
`GoLean/GoCore/{Machine,Ops}.lean`, `GoLean/CLI.lean`,
`GoLean/NativeToIR.lean`, `tools/nativefrontend/*` (except `declaration*`)
byte-identical to main. Any "unknown identifier" among `utf8String?`,
`firstPanicLine?`, `renderStringMember`, `PanicText.*`, `stringPanicHead`
is a coupling; the module moves to L1-T. The grep pre-check done for this
plan found exactly the files named above and nothing else in L1.

**Fixes applied in-chunk (by finding id).**
- **B-R2** — one sentence in `GoLean/Interface.lean`'s facade docstring:
  both typed profiles are choice-free (`Control.no_spawn/no_select/
  no_seq_consumption`, `Inv.run_choices : chf = ch`), so the `∀ ch`
  quantifier on `runProgramPool_typed` is uniform by vacuity and carries no
  nondeterminism evidence; F2 remains open for the typed contract (L6
  records it in the §7 table).
- **B-R20** — `docs/2026-09-06_b7-context-store-design.md:135`: replace
  "the existing host-capability ruling" with "the host-capability decision
  remains open and [USER]-owned (master plan §3.E, line ~1402)"; no such
  ruling exists.
- **B-R21** — the `typed_contract_review` sealed artifact was edited
  in-place by a corrigendum (that hunk is `ff7173dd`'s, → L3). L1 lands the
  review WITHOUT it; L3 lands the correction as a SEPARATE dated
  disposition (its own file or a dated section in L3's landing note),
  leaving the sealed text untouched.
- **A-R11** — `scripts/check-declarations` prints `sha256sum` lines and
  never compares them: either track the expected hashes (`Tests/
  declaration-fixture/SHA256SUMS`, checked with `sha256sum -c`) or rename
  the step so it does not read as a pin. Recommended: track.
- **A-R12** — `declaration.go:100` calls `e.localTypeOrdinal(obj)`, which
  writes `e.badLocalTypes` — a set the EXECUTABLE emit's
  `checkLocalTypeOrdinals` consumes. Give the serializer its own scratch
  set (or a read-only query), so exercising it cannot poison the executable
  emit; fix the two silent-default nits (`declaration.go:17-23`, `:99-103`
  — a nil-package object must refuse, not emit `"package": ""`).
- Auditor A's caveat on `StringPanic.renderStringMember_bytes_or_escape`
  (near-tautological) is L3's; nothing in L1 cites it.

**Exclusions.** Every behavioural change to `GoLean/GoCore/Machine.lean`,
`GoLean/GoCore/Ops.lean`, `GoLean/GoCore/PanicText.lean`,
`GoLean/GoCore/StringPanic.lean`, `GoLean/CLI.lean`, `GoLean/NativeToIR.lean`
(unchanged on the branch anyway), and any existing frontend file (none
changed on the branch). `Tests/InterfaceContract.lean` (no L1 delta).
L1-T (above). All `docs/evidence/`.

**Dependencies.** L2 landed (L1's proof-step `scripts/ci` hunks are
appended to a `scripts/ci` that already carries L2's). **Gate.** Fresh
`scripts/capped scripts/ci --diff` (the baseline must not move: L1 adds no
corpus rows and no runtime change — a moved baseline is a finding);
`spikes/iris-customer/check` (outside the gate graph, run and recorded);
`spikes/gate-a1` build. **Audit focus.** Vacuity and false uses of the
exported theorems (auditor B's method: `#eval checkTypedBoolean` on the
native fixture, the `¬ BoolHeap illTyped` probe, axiom lists `[propext,
Quot.sound]`/`+ Classical.choice`); that the profiles' stated smallness
matches their grammars (no calls/loops in Boolean; recovery adds direct/
closure calls, defers, string panic, recover, finite call graph); that the
seven new steps fail closed; that the spike stays outside the default
build (`lakefile.toml` `defaultTargets` unchanged; root lakefile has no
`[[require]]`; no `GoLean/`→`spikes/` import — auditor B verified all
three at the tip, re-verify at the landing tip); L1b's zero effect on
executable wire bytes. **[USER] decisions needed.** None beyond D3; the
"Gate C exit criterion is NOT met" statement (`spikes/iris-customer/
README.md:98`, "still uses machine internals and unfolds operations") is
kept verbatim in L1's note — no landing note may imply otherwise.
**Credits.** Implementation: `c7a439f7`, `f251abcb`, `354ef7f2`,
`8717b974`, `26f0dc09`, `e8a665e9`, `4f7aedef`, `63769964`, `f160d7ca`,
`10cd6e8f`, `04109912`, `45ff4ae2`, `c53bb6a7`; integration: `a392fab0`,
`5158589a`, `29092c26`, `77f154e0`, `123fd48e`, `30b09c08`, `b3d6fa6e`,
`658fe3eb`, `b34cee67`, `414a2abe`, `7bd32ad6` (non-terminal parts),
`7edc298f`; reviews: `d3ffb32b`, `ce896516`, `71183a62`, `23aff3ea`,
`3d150a84`, `815227ad`, `fadcb0c3`, `761d4e28`, `638af8dd`, `8b5ce690`,
`1ae77483`, `c2057e78`, `0079ece9`, `efc2712c`, `4158368f`, `f5f228ca`,
`1078c910`, `bfecf455`, `e4318e01`, `bd31dd5d`, `53ca910a`, `f3971190`.
L1b: `298e4da1`, `0ff12435`, `b9136a05`, `8ea5a74b`, `f3913e06`; reviews
`7ae7fc0a`, `cf13789f`, `18f90eb9`, `798e9c76`, `7ac3eb46`, `4d492cea`,
`3cdde025`, `60f541c6`, `2a70246f`, `39235f65`.

### 2.3 L3 `land/panic-text-tape`

The rendering work, redone per doctrine ("No semantic choice hides in
evaluator recursion"; "Fail closed, always"; "a visible red beats a hidden
wrong answer"). Heavy audit. Frontend and `NativeToIR` untouched, so no
5a. **Contents (45 paths + its hunks of the 11 H files):** `GoLean/GoCore/
Machine.lean`, `Ops.lean` (comment), `PanicText.lean`, `StringPanic.lean`,
`GoLean/CLI.lean`, `Tests/{PanicRendering,StringPanicMembers,
InterfaceContract}.lean`, the corpus dirs `panic-recover/{panic-text,
repanic-same-value-abort,string-members}/`, `Corpus/controls/
string-members/**`, `baselines/string-members/**`, the string-member
tooling (`tools/string_member*.py`, `tools/test_string_member.py`,
`tools/check_string_member_fixtures.py`, `scripts/check-string-members.py`,
`scripts/coverage-manifest`, `scripts/coverage-baseline-diff`), the ten
notes `docs/2026-09-06_{panic-rendering-repair,
historical-string-member-argument,string-*}.md`, and L1-T (§2.2). Much of
this list is REWORKED or RETIRED below, not landed as at the tip.

**(a) Valid-UTF-8 first-line-suffix widening — a gc-verified strict-lane
FIX; lands.** From `ff7173dd`: `asciiString?` → strict constructive
`utf8String?` (the same decoder as string range/conversion; invalid →
`none`), suffix formatting BEFORE first-line projection. gc agrees
(`printpanicval` → `printindented` prints the whole payload, then
` [recovered]`; the first line is the payload's first line — Appendix B).
Evidence: the nine `panic-recover/panic-text/*` rows and the
`panic-newline-abort` FAIL→PASS are STRICT-lane rows with real gc text
comparison (auditor A: "that half is good work"). Lands with: the
`Machine.lean`/`Ops.lean` hunks of `ff7173dd`, `Tests/PanicRendering.lean`
restricted to valid-UTF-8 cases, the panic-text corpus and its 10 baseline
rows, BUG-004's item-3 hunk ("FIXED 2026-09-06") and its `Cases:` line
losing `panic-newline-abort`, the ledger's A7 note and §8w movement,
`docs/2026-09-06_panic-rendering-repair.md`. `PanicText.lean` lands only
its `firstLine`/`firstLine_bytes` half (the two `decide +kernel` over
`Fin 256` are kernel, doctrine-permitted); `escapeAllBytes` and its
theorems do NOT land (see (c)).

**(b) The `[recovered]` / `[recovered, repanicked]` suffix — DETERMINED
from gc source at the pin (Appendix B; `deps/go/src/runtime/panic.go`
at `c19862e5f8` = go1.26.5):** the marker is a deterministic function of
eface IDENTITY (type word AND data pointer, `preprintpanics` line 715:
`*efaceOf(&p.link.arg) == *efaceOf(&p.arg)` → `p.link.repanicked = true`;
`printpanics` 749–753 prints ` [recovered, repanicked]` iff `recovered &&
repanicked`, and 737 suppresses the newer duplicate line). Identity is:
(i) FORCED-COLLAPSE when the re-panic passes the recovered interface value
itself (`panic(r)` with `r := recover()` — the same eface bits; the
sprint's `Equal`/`Multiple`/`repanic-same-value-abort` are this shape, so
gc's `[recovered, repanicked]` there is not a draw the machine may miss —
A-R1's second reproduction); (ii) FORCED-DISTINCT when at least one side is
a fresh runtime boxing of a non-empty string (`convTstring` allocates) —
` [recovered]` plus a second line; (iii) LAYOUT-DEPENDENT LATITUDE when
both sides are independently boxed constants the compiler/linker may share
(the `"or"+"ig"` constant-folding probe in `Machine.lean`'s own comment;
the empty string's shared `zeroVal`). The spec fixes none of the text
(R-1, `docs/2026-08-20_w32-re-envelope-charter.md:28-50`). Therefore:
**neither "implement exactly" nor "pure latitude" alone is honest; the
machine lacks boxing identity, so the fact it cannot decide is REIFIED as a
choice, exactly as the BUG-087 panic-text ruling did (R9a two-member
envelope, `docs/BUGS.md` BUG-087; PASS/membership).** Design for the L3
worker:
- `renderPanicHead state first rest`: unequal adjacent payloads →
  ` [recovered]` (forced, deterministic — unchanged); EQUAL adjacent
  payloads (`e.value == first.value`, any payload family, not only strings)
  → the collapse is a `ChoiceSite` (new constructor, e.g. `.panicCollapse`)
  consumed at the transition that produces the abort terminal, with total
  relational rule shape (merge invariant, `AGENTS.md`): member 0 renders
  `base ++ " [recovered, repanicked]"` and suppresses the duplicate; member
  1 renders `base ++ " [recovered]"`. The chain can now EXPRESS
  `repanicked`. The old unconditional `some (base ++ " [recovered]")` for
  strings (A-R2) is deleted; the old `none` is replaced by the choice, not
  by a member.
- "Both members certified" (the brief's condition, per BUG-087): the corpus
  carries a gc witness for EACH member — (i) `Equal`-shape rows for the
  collapse, (ii) a runtime-computed-equal-string re-panic row for the
  non-collapse — so both are gc-producible renderings, and the rows run in
  the MEMBERSHIP lane (`--engine dedup` enumerates both streams; K gc
  draws ∈ the set). `repanic-same-value-abort` moves
  FAIL/lean-observation → PASS/membership with `why` recorded, the way
  BUG-087's rows did, and the row's `cases.tsv` keeps a gc text pin in
  `expected_reason` (the branch dropped it to `-`: A-R2, restored).
- The fail-closed `none` is RESTORED wherever the model still cannot
  render: non-string equal-payload identity that a choice would over-widen
  (the worker decides per family and says why), and every (c) case below.
- `Tests/PanicRendering.lean` / `Tests/StringPanicMembers.lean` theorems are
  restated choice-indexed; `StringPanic.lean`'s total-renderer theorems
  (`renderStringMember_*`, `stringPanicHead`, `abortMsg_string`) are
  retired with the total renderer; L1-T is restated over `abortRecord?`
  (§2.2).

**(c) Invalid UTF-8 payloads.** gc writes the raw bytes to stderr
(`printindented` byte-copies). The compared observation is
`golean-observation-v1` with a `String` message; a `String` cannot carry
invalid bytes, and adding a bytes variant is an observation-schema change
(an observation-policy decision, not L3's — §4 D5). Therefore L3 does the
fail-closed thing: `renderPanicPayload` returns `none` for a string payload
whose bytes are not valid UTF-8 (the pre-existing refusal, restated over
`utf8String?`), the `invalid-{before,after}-lf` and `invalid-recovered`
rows land RED (FAIL/lean-observation) on BUG-004's `Cases:` line with the
gc bytes recorded in the entry, and **no `"\xHH"` form Go never prints is
ever emitted** (A-R3, B-R3 envelope point). If the [USER] later rules for a
byte channel (the harness already transports `messageBytes` in
`--abort-record`), those rows flip green in a strict byte comparison, not
in a membership quotient.

**(d) The string-member lane, with A-R1 fixed.** Under (b)+(c) the lane's
three purposes are covered elsewhere: collapse → membership lane; valid
text → strict lane; invalid bytes → red until a byte channel exists. What
remains of the lane is a third comparison mode whose only reviewed use is
now redundant. **Recommended default [AGENT]: RETIRE the lane** —
`tools/string_member*.py`, `tools/test_string_member.py`,
`tools/check_string_member_fixtures.py`, `scripts/check-string-members.py`,
the `scripts/ci` "explicit string-member apparatus" step, the lane
vocabulary in `scripts/{diff-coverage,coverage-manifest,
coverage-baseline-diff}`, `GoLean/CLI.lean`'s `native-json-string-run` (keep
only if a consumer remains), and `Corpus/controls/string-members/**` (its
13 control roles — 8 exact-equality non-abort roles — become ordinary
strict rows where they add coverage; the rest are dropped). Alternative
(if the [USER] wants the lane kept): apply A-R1's fix verbatim (compare
`bytes(raw_go["messageBytes"])` against the encoded member set; add the
gc-message mutation to `scripts/check-string-members.py:77`), expect the
reds A-R1 predicts, and keep it within R-1's terms ("the payload's KIND …
compared exactly", "the conversion must not relax them") — a quotient
still checks that gc's draw lands in the class. Either way, no row is
green on a text axis nobody compared. §4 D2 decides the lane's fate; the
reds land immediately in both options.

**(e) `baselines/string-members/`** — RETIRED with the lane (default), or,
if the lane is kept: brought under the re-pin guard loop
(`scripts/ci:912` `for GUARD_BASE in …` extended to the JSON pins with the
same BUGS.md `Cases:` rule), given a tracked regenerator with a `--bless`
mode that refuses without a written reason, and B-R8(revised)'s 17,970 B
`apparatus_sources` block hoisted into one file referenced by sha256 (it
is byte-identical across all nine pins, 57% of the dir, and rewrites on
every core edit — a guaranteed train conflict). A-R4.

**Other fixes in-chunk.** B-R21 (the separate dated disposition of the
`typed_contract_review` corrigendum); BUG-004 hunks re-expressed to match
what actually landed ((a) fixed; (b) reified; (c) red; the "R-1 authorizes
a uniform ` [recovered]` suffix" docstring sentence deleted); the ledger's
§8z paragraph replaced by L3's measured movement; `baselines/native-full.tsv`
re-pinned once at L3's tip with a full run; `docs/2026-09-06_string-*`
notes land only insofar as they describe what lands — the assessment,
implementation, certificate-design and production-review-request notes
are ARCHIVED (branch only) if the lane is retired, with a one-paragraph
pointer in L3's landing note.

**Exclusions.** Everything L2/L1/L4 own; all `docs/evidence/` except L3's
own gate tails and the small gc witness transcripts for (b)(i)/(b)(ii)/(c)
(`go run` under the pin, a few KB each — these ARE the "small
witness/probe files" principle 5 allows). **Dependencies.** L2 (the byte
view `--abort-message`/`--abort-record` the witnesses use), L1 (the
Interface facade L1-T restates against), L4 (its rows share the
`panic-recover/` tree and BUGS.md region; landing L3 after L4 avoids a
second reconciliation of the same hunks). **Gate.** Fresh full
`scripts/capped scripts/ci --diff` at the ruled worker count; the
membership-lane self-test `scripts/test-lane-validation`; the three
witness reproductions re-run and their bytes compared to the transcripts.
**Audit focus.** That no member of any envelope is a rendering gc cannot
produce (upper bound) and that gc's draw is checked ∈ the set on every
row (lower bound, A-R1's exact defect); that the choice is consumed on the
tape with a total rule shape and no default arm; that `none` is restored
for every case the model cannot decide; that
`renderStringMember_bytes_or_escape` and the total renderer are gone, not
renamed; that the lane's retirement removed every gate step, vocabulary
word and pin together (a gate that cannot run must fail, not skip). **[USER]
decisions needed.** D2 (lane retire vs keep; reds now), D5 (R-1's scope
and a future byte channel — B-R3's question, posed explicitly: "does R-1
extend to explicit-string payloads, and may a non-Go-producible escape
member ever be a member?" — this plan's answer is NO to the second half
by doctrine; the first half is settled by (b)'s membership design without
extending R-1's text). **Credits.** `ff7173dd`, `82e177c7`, `c7eeaf57`
((a)); `819182b5`, `ccf826cb`, `c969079a`, `4a8a8ad1`, `e6a99203`,
`731beb0b`, `bb850710`, `f0829091`, `91efd4ca`, `563c01de`, `b5dd4076`
(assessment note) — as the ORIGIN of the work L3 reworks, credited as such.

### 2.4 L4 `land/observer-terminal`

**Contents (5 paths + hunks).** `Corpus/coverage/exec/panic-recover/
panic-controls/{cases.tsv,main.go}` (9 rows: NUL, SOH, TAB, CR, newline,
recovered-newline, output-prefix, output-ok, child-confluent) and
`panic-markers/{cases.tsv,main.go}` (11 rows: forged `fatal error:`
prefixes, fake traces, glued output, printed continuations); their 20
baseline rows (all born PASS at the tip) with L4's own measured header;
`docs/BUGS.md` BUG-105 (fixed; its `Cases:` line names the 9
panic-controls rows — so BUG-105 cannot land before those rows, and they
cannot land without it); `docs/2026-09-06_observer-controls-repair.md`;
the ledger's §8x movement (and the row-part of §8y) re-expressed as L4's
measured movement; and a NEW records note `docs/2026-09-07_observer-
terminal-landing.md` whose REQUIRED section is the observation-schema
compatibility statement: (1) cached certified sets — `--read-observation`
returns the harness JSON bytes unchanged (no re-encoding), so
`baselines/certified/*.certified.tsv` byte-compatibility is preserved
(auditor A verified; the worker re-verifies by re-reading one certified
observation through the new path and `cmp`-ing); (2) K sampling — the
membership lane's `MEMBERSHIP_DRAWS`/`membership_go_observation` now reads
stderr via `grep -aqF` and the checked byte view instead of shell
substitution, changing no draw count and no accept rule beyond the
classifier's refusals, which are enumerated; (3) stage alternation — the
baseline's declared stage alternations are preserved row-for-row (the
branch's header says so for each re-pin; L4 re-derives it with
`scripts/coverage-baseline-diff`); (4) `GOTRACEBACK=system` changes the
oracle's stderr for every aborting case — the program-output `output`
field is unaffected because the split happens at the authenticated report
boundary; the worker shows one before/after stderr pair. **Fixes.** None
of its own (A-R6 is L2's; BUG-106 landed in L2). It restores the corpus
globs L2's `check-observer-controls.py` hashes. **Exclusions.** All
`docs/evidence/` except L4's gate tails and one before/after stderr pair.
**Dependencies.** L2 (the harness and runner), L1 (order only).
**Gate.** Fresh full `scripts/capped scripts/ci --diff`; 20 born rows, 0
flips expected — any flip is a finding. **Audit focus.** That the 20 rows
exercise what BUG-105/106 claim (byte transport of control bytes; forgery
refusal); that the compatibility statement's four points are each
demonstrated, not asserted; that `Corpus/controls/` is NOT in this chunk
(it is L3's). **[USER] decisions.** D3; D4 was taken at L2. **Credits.**
`d0dbd469`, `b5dd4076`, `563c01de`, `a34bc969`; reviews `9726046c`,
`a6df5cb3`, `838adc51`, `4bfeba58`.

### 2.5 L5 `land/uintptr` — HELD for a [USER] ruling; nothing built until ruled

The `uintptr` repair is NOT at the tip; it exists as branch
`typed-uintptr-identity` @ `5f185fb3` and as the sprint worktree's staged,
uncommitted merge (B-R1). Two standing records, neither cited by the
repair, its BUG-107 entry (`docs/BUGS.md:6336-6380`, staged) or its ledger
movement (§8z-uintptr, staged): `docs/2026-08-21_w7-desugar-inventory.md:
2740` — «**`uintptr` is a gc-pin of latitude R1** — record it there rather
than "fix" it» (J-8), and `docs/2026-08-11_latitude-inventory.md:1766`,
latitude row R1: «`uintptr` (frontend maps to uint64; observations of it
refused)». The repair un-refuses a refused observation kind ("The Go
observer and Lean observation decoder carry `uintptr` explicitly",
`docs/2026-09-06_uintptr-identity-repair.md:42-45`, staged) and edits
`GoLean/NativeToIR.lean` (so 5a fires) and four `GoLean/GoCore/` modules
(B-R13). Options for the ruling (§4 D1):
- **(a) Record per w7 / R1:** `uintptr` stays a gc-pin of latitude R1; the
  type-identity half of the finding (that `uintptr` is a distinct type
  from `uint64` for identity, method sets and assertions — sound and
  K3-eligible per auditor B) is recorded as a BUG entry with red-first
  rows and a plan, observations of `uintptr` stay refused, BUG-107's
  number is reserved for it. No trusted-surface change.
- **(b) Fix, with the records amended:** land `5f185fb3`'s repair as its
  own chunk after a third-lane review of the latitude override
  specifically; the landing note cites and supersedes w7 J-8 and latitude
  row R1 (amending both records, with the register-extension consequence
  spelled out), reconciles BUG-107 (currently a number carried only in a
  staged file and in an evidence copy — B-R17), re-measures the PROVISIONAL
  3,643 union baseline with a real full run (`docs/2026-09-06_typed-sprint-
  pause-state.md:56-58`: "an exact three-way union, not a measured combined
  full run"), and runs `scripts/ci --slow` with a refreshed certification
  record (5a).
Until ruled: no worktree, no branch, no BUG-107 entry on main. L6 records
the number as HELD.

### 2.6 L6 `land/sprint-records` — LAST

**Contents (5 paths + new files).**
- `docs/2026-09-05_typed-consumer-sprint-charter.md` — landed trimmed to
  what was ruled and executed; every [USER] quote relay-marked (B-R18: the
  kickoff quote «Agree with all 5» and the K4 clarification «merges *to
  main* are always user-approved. Feature branches can be merged to by
  agents, when standign approval is given by the user» stay verbatim, typo
  included, and gain "relayed by the [AGENT] coordinator — cite as
  relayed").
- `docs/2026-09-05_typed-consumer-sprint-handoff.md` — trimmed; the status
  line and the O1–O5 outcome table refreshed to the truth at landing
  (B-R6); the decision ledger CORRECTED (B-R15): the line "No critical
  issue has yet been identified" is replaced by an itemised table of the
  audit findings that were §7-class decisions (BUG-106 terminal
  classification, B-R14; the uintptr latitude override, B-R13; the R-1
  authority reading, B-R3/A-R2/A-R3; the withdrawn B7 V1 kernel-sharing
  completeness claim) each with reproducer, affected claim, rule,
  alternatives, recommendation, cost of deferral; the `.tmp` cleanup
  sentence (handoff:832, "The user's authorized primary `.tmp` cleanup
  removed 68,122 files") gets a ledger entry with the [USER] text or is
  downgraded to [AGENT] (B-R23).
- The honest pause-state record TRACKED (B-R16): `docs/2026-09-06_typed-
  sprint-pause-state.md` copied from the sprint worktree (untracked there)
  verbatim, with a header noting it is the paused-state snapshot and that
  its "Follow-up retirement disposition" section's [USER] attribution is
  UNQUOTED (§5). Also tracked: `docs/2026-09-06_c1-contract-handoff.md`
  (charter §4's C1 deliverable, marked DRAFT as it is), and the two
  landing audits (`docs/2026-09-07_landing-audit-A.md`, `-B.md`, verbatim
  from `.tmp/landing-review/`) — they are the closing reviews and the
  source of every finding id in this plan.
- Whole-file BUGS.md copies DROPPED (they are not landed by anyone —
  they are evidence payload) and **BUG-107 reconciled** (B-R17): no `## BUG-
  107` reaches `docs/BUGS.md` until L5 is ruled; L6 adds one line to
  BUGS.md's numbering note reserving 107 as HELD with a pointer to §2.5,
  so the next lane does not reuse it.
- Relay markers on every [USER] quote in the five files (B-R18).
- `docs/evidence/2026-09-07_typed-sprint-landing/MANIFEST.tsv` — one row
  per file NOT landed from the tip's `docs/evidence/**` (2,159 rows, plus
  the rows for anything dropped from the other chunks): `path\tsha256\tbytes\
  torigin_commit`, generated by `git ls-tree -r -l typed-consumer-sprint --
  docs/evidence` + `git log --format=%h -1 <tip> -- <path>` (the blob's
  sha256 via `git cat-file`), ≈ 250 KB — it lands as the ONE grandfathered
  exception above 256 KiB if it exceeds the cap (listed in
  `SIZE-ALLOWLIST.tsv` by hash), or is split per source dir. Its README
  states that the bytes are on branch `typed-consumer-sprint` @ `7edc298f`
  and records auditor B's payload quantification (734,510 lines / 2,159
  files / 114,156,315 B; 36 archives 55.9 MB; 345 exact source copies;
  511 intra-payload duplicates).
- `docs/2026-09-05_master-plan.md` §7 addendum (replacing the branch's +21
  stale checkpoint lines): sprint outcome — **O1, O2, O3 partially landed
  (L1/L2/L4 + what L3 lands), O4 unimplemented (`grep ProgramCtx GoLean/`
  returns one deferral comment in `Platform.lean:19`; B7 lives on
  `typed-context-store` @ `ca1e01d5` with substantial uncommitted work;
  the I1 envelope on `typed-i1-envelope` @ `3d49e9e9`), O5 pending**; and
  the F2/F3/F5 rows updated with auditor B's answer table (§1 of
  `docs/2026-09-07_landing-audit-B.md`), reproduced IN FULL verbatim in the
  addendum — the verdict cells, excerpted here: F2 «**Partially answered, but not by this branch, and not for
  the typed profile.** The `∀ ch` quantifier on the typed theorems is
  *vacuously uniform* — the profiles are deterministic. The reverse
  direction (relation → driver) for the true Prop-level relation is still
  absent»; F3 «**Answered, honestly, by the "basic `Language` without
  `EctxLanguage`" route the audit itself allowed.** It is **not** an
  `EctxLanguage` instance and does not claim to be»; F5 «**Answered
  *within two deliberately tiny profiles*, and stated as such.** … **But
  `StateWf` itself is unchanged**: `decide (StateWf illTyped)` still
  returns `true` at the tip. The exclusion is profile-local, not
  machine-wide». Plus the Gate C note: the "no unfolding of internals"
  exit criterion is NOT met (`spikes/iris-customer/README.md:98`).
- `AGENTS.md`: the committed sprint pointer rewritten — the sprint is
  closed; its work landed per this plan; history on the archive branch.
- `CLAUDE.md`: NOT touched by L6 (the branch's retitle is rejected —
  B-R4; §4 D6 decides whether K4 is recorded at all).

**Exclusions.** Everything above 256 KiB except the manifest; every
`docs/evidence/` file of the tip (the manifest replaces them); the
uncommitted storage-maintenance docs (`docs/2026-09-06_storage-*`,
`docs/storage-operations.md`, `scripts/go-cache`, `tools/storage*.py`,
`tools/audit_scratch.py`) — §5. **Dependencies.** All other chunks landed
or ruled (L5 may still be HELD; the addendum says so). **Gate.** `scripts/
capped scripts/ci --diff` (docs-only; the evidence-size gate from L2 must
pass on the manifest). **Audit focus.** That every [USER] assertion traces
to K1–K5, a pre-existing ruling, or the 2026-09-07 ruling, and is marked
relayed; that no ledger copy survives anywhere on main; that the outcome
table claims nothing the landed chunks do not prove; that the manifest's
row count equals the tip's evidence file count. **[USER] decisions.** D6.
**Credits.** `5a4aca9e`, `10fefeb3`, `c53bb6a7` and the seventeen handoff
checkpoints (Appendix A, `docs/2026-09-05_typed-consumer-sprint-handoff.md`
row).

## 3. Order and dependencies

```
L2 gate-tooling ──► L1 typed-core-proofs (+L1b) ──► L4 observer-terminal ──► L3 panic-text-tape (+L1-T) ──► L6 sprint-records
                                                                                   ▲
L5 uintptr ── HELD on §4 D1 ── if (b): its own chunk after L3, with --slow (5a) ───┘ (before L6, or L6 records HELD)
```

- L2 first: every later chunk's gate runs on its harness; its evidence
  gate polices every later chunk's evidence dir; its BUG-106 flip is the
  only PASS→non-PASS any chunk carries.
- L1 second: no runtime change, no corpus change; the largest and least
  controversial payload; L1b inside it with its own gate line.
- L4 third: rows only, on L2's apparatus.
- L3 fourth: the reworked renderer, the choice site, the reds, L1-T's
  restatement — the heavy audit, done once, after the tree around it is
  settled.
- L6 last: it can only describe what landed.
- L5: nothing until §4 D1.
- Merge-protocol step 5a is owed by NO chunk here (`wire.go`,
  `NativeToIR.lean` unchanged at `7edc298f`); it is owed by L5(b).
- Each chunk re-pins `baselines/native-full.tsv` at most once, with its own
  fresh full run and written reason in the header, and the header keeps
  the previous pin's record (the branch's convention, kept).

## 4. [USER] decisions

| # | decision | options | [AGENT] recommendation | blocks |
|---|---|---|---|---|
| D1 | `uintptr` (§2.5, B-R13) | (a) record per w7 J-8 / latitude R1, reserve BUG-107; (b) fix with records amended, third-lane review, real full+slow run | (a) now; (b) as its own later arc if the type-identity half is wanted as a fix — the observation un-refusal is the part that needs the ruling | L5 |
| D2 | the `string-member` lane (§2.3(d)/(e); A-R1, A-R4) | retire (default) vs keep with A-R1's fix; in both, `invalid-*` rows go RED immediately on BUG-004's `Cases:` line and the `Equal`-shape rows move to membership | retire | L3 |
| D3 | coverage worker count (A-R5, B-R22) | the recorded "2" vs the runner's default (`GOLEAN_COVERAGE_JOBS` = `nproc` when unset — 32 on this box) | **Finding: no verbatim [USER] ruling of "2 workers" exists in any tracked file.** The figure appears only in sprint-era records written by agents: `docs/2026-09-06_observer-controls-repair.md:128` (commit `d0dbd469`, "coverage workers 2" as a run parameter), `baselines/native-full.tsv:15` ("future conformance explicitly uses 2"), `docs/language-coverage-ledger.md:2074-2076` (branch), `handoff:669` ("two workers"), and the UNTRACKED `docs/2026-09-06_typed-sprint-pause-state.md:19` ("Limits remain 16 GiB, 3 Lean threads, 2 coverage workers" — no quote, no relay marker). It reads as a sprint-scoped lane-coordination envelope, not a standing rule; the charter (§6) says only "within the existing resource envelope". Recommendation: the [USER] states the number once; until then every chunk's gate RECORDS its `jobs` (the run meta already does) and uses ≤ nproc/2 on this shared box. | every gate |
| D4 | B-R14 — is the crash channel + `GOTRACEBACK=system` + fatal-unwind refusal an observation/terminal-policy change to ratify? | ratify via L2's sign-off; or refuse → L2 re-cut to byte transport (`d0dbd469`) only | ratify: direction fail-closed, one row's PASS lost honestly, forgery counterexample preserved | L2 |
| D5 | B-R3 — R-1's scope for explicit-string payloads; a byte-level observation channel for invalid UTF-8 | (i) no byte channel now: `invalid-*` red (default); (ii) add a bytes variant to `golean-observation-v1` (schema change, own arc) | (i) now; the non-Go-producible escape member is never a member | L3 |
| D6 | B-R4 — record K4 ("merges to main are always user-approved; feature branches may be merged by agents under standing approval") in `CLAUDE.md` at all? | not landed (default — sprint-scoped, sprint over); or a one-line note inside merge-protocol step 5, verbatim, relay-marked, approval-scoped only | not landed | L6 |
| D7 | the evidence caps (§2.1) | 256 KiB / file, 4 MiB / dir, no archives, no source copies — PROPOSED [AGENT] | as proposed; main needs an 18-entry allowlist either way | L2 |

## 5. Out of scope

- Branches `storage-maintenance-20260906` (`0560484e`) and
  `storage-maintenance-main-20260906` (`521f4eca`) and their worktrees:
  NOT reviewed by either audit or by this lane. Their content overlaps the
  sprint worktree's uncommitted overlay (`scripts/go-cache`,
  `tools/storage*.py`, `tools/audit_scratch.py`, `docs/2026-09-06_storage-
  *`, `docs/storage-operations.md`, `scripts/ci` +12/−3, `scripts/diff-
  coverage` +5/−1, `docs/agent-sandbox.md`) and — per B-R5/B-R19 and the
  pause-state record's "Follow-up retirement disposition" — an
  `AGENTS.md` "Retired Worktrees" section asserting standing deletion
  approval. **Before any of it lands, its `AGENTS.md`/worktree-deletion
  content must be checked against the same rule that rejects the sprint
  worktree's hunk (§1 item 1): no standing or implied permission for
  destructive operations; [USER] statements verbatim and relay-marked or
  downgraded to [AGENT].** A "retired lanes" policy, if the [USER] wants
  one, is a separate records decision with its own audit.
- The other sprint lane branches (`typed-context-store` @ `ca1e01d5`,
  `typed-i1-envelope` @ `3d49e9e9`, `typed-byte-runtime` @ `35aee5d3`, the
  `typed-*-review` branches): unmerged into the sprint tip, unreviewed
  here; L6's addendum names them as where O4's work lives.
- The primary checkout's untracked `docs/2026-09-06_disk-growth-review.md`:
  not this lane's.

## 6. Provenance

- [AGENT] records worker, lane `landing-plan-0907`, worktree
  `.claude/worktrees/landing-plan-0907` off main `47195683`, 2026-09-07.
- Read in full: `CLAUDE.md`, `AGENTS.md`, both landing audits
  (`.tmp/landing-review/auditor-{A,B}.md` in the sprint worktree, 24,250 and
  55,035 bytes), the sprint charter and handoff at `7edc298f`,
  `docs/2026-09-05_master-plan.md` §7, the untracked pause-state and C1
  handoff (read-only), `deps/go/src/runtime/panic.go` (`preprintpanics`,
  `printpanics`, `printPreFatalDeferPanic` at the pin), the branch's
  diffs of `Machine.lean`, `Ops.lean`, `CLI.lean`, `scripts/ci`,
  `scripts/diff-coverage`, the harness, the baselines header, BUGS.md, the
  ledger, `lakefile.toml`, `CLAUDE.md`, `AGENTS.md`, and the import lines of
  every new Lean module.
- Derivations: `git diff --name-only main...typed-consumer-sprint` (2,410
  paths); `git log --format=%h main..typed-consumer-sprint -- <path>` per
  non-evidence path (Appendix A); `git ls-tree -r -l` and `git ls-files -s`
  blob-hash comparisons for the size-gate calibration; the L1 coupling grep
  (§2.2). No lake/lean build was run for this plan; the coupling is
  established by import lines and symbol use, and §2.2 gives the build
  procedure that confirms it.
- Nothing on main, on the sprint branch, in the sprint worktree, or in
  `deps/` was modified. No process was killed. No push.

## Appendix A — the partition (every non-evidence path at `7edc298f`)

Derived 2026-09-07 from `git diff --name-only main...typed-consumer-sprint` (2,410 paths) and, per path, `git log --format=%h main..typed-consumer-sprint -- <path>` (the `origin` column, newest first). `H:` marks a hunk-split file and names the other chunks that take hunks of it; the file is counted once, here. The 2,159 `docs/evidence/**` paths are NOT landed (§1 item 5, §2.6 MANIFEST) and are not listed. Unclassified: 0. `spikes/iris-customer/GoLeanIris/Terminal.lean` is listed under L1 by whole-file rule but moves to L1-T by the §2.2 coupling finding.


### L2 `land/gate-tooling` — 27 paths

```
baselines/native-full.tsv	[819182b5,b5dd4076,d0dbd469,ff7173dd]	H:L3,L4
docs/2026-09-06_observer-classifier-repair.md	[b5dd4076]
docs/2026-09-06_observer-crash-channel-design.md	[b5dd4076]
docs/2026-09-06_observer-diagnostic-tools.md	[2b679404]
docs/2026-09-06_observer-terminal-classification-design.md	[b5dd4076]
docs/BUGS.md	[819182b5,b5dd4076,d0dbd469,ff7173dd]	H:L3,L4
docs/language-coverage-ledger.md	[819182b5,563c01de,d0dbd469,ff7173dd]	H:L3,L4
scripts/cedar-census	[2b679404]
scripts/check-observer-controls.py	[b5dd4076,d0dbd469]
scripts/check-observer-tools.py	[2b679404]
scripts/ci	[7edc298f,7bd32ad6,c969079a,819182b5,2a70246f,414a2abe,563c01de,0ff12435,04109912,2b679404,f160d7ca,63769964,4f7aedef,e8a665e9,d0dbd469,8717b974,c7a439f7]	H:L1,L3
scripts/diff-coverage	[819182b5,b5dd4076,d0dbd469]	H:L3
scripts/gotest-triage	[2b679404]
scripts/membership-sampling	[2b679404]
scripts/test-lane-validation	[b5dd4076]
tools/coverageharness/abortkind.go	[b5dd4076]
tools/coverageharness/abortkind_test.go	[b5dd4076]
tools/coverageharness/abortrecord_test.go	[819182b5]
tools/coverageharness/crashhook.go	[b5dd4076]
tools/coverageharness/crashhook_test.go	[b5dd4076]
tools/coverageharness/crashview.go	[b5dd4076]
tools/coverageharness/crashview_test.go	[b5dd4076]
tools/coverageharness/main.go	[819182b5,b5dd4076,d0dbd469]
tools/coverageharness/observe.go	[819182b5,b5dd4076,d0dbd469]
tools/coverageharness/observe_test.go	[b5dd4076,d0dbd469]
tools/coverageharness/split.go	[b5dd4076,d0dbd469]
tools/coverageharness/split_test.go	[b5dd4076]
```

### L1 `land/typed-core-proofs` — 143 paths

```
GoLean/GoCore/AbortObservation.lean	[04109912]
GoLean/GoCore/BooleanControl.lean	[8717b974]
GoLean/GoCore/BooleanControlTyping.lean	[8717b974]
GoLean/GoCore/BooleanInitialization.lean	[354ef7f2]
GoLean/GoCore/BooleanInvariant.lean	[26f0dc09,8717b974]
GoLean/GoCore/BooleanPool.lean	[26f0dc09]
GoLean/GoCore/BooleanPreservation.lean	[8717b974]
GoLean/GoCore/BooleanProgram.lean	[26f0dc09]
GoLean/GoCore/BooleanProgress.lean	[8717b974]
GoLean/GoCore/BooleanSafety.lean	[8717b974]
GoLean/GoCore/BooleanSetup.lean	[f251abcb]
GoLean/GoCore/BooleanStore.lean	[f251abcb]
GoLean/GoCore/BooleanTyping.lean	[c7a439f7]
GoLean/GoCore/RecoveryAdmission.lean	[e8a665e9]
GoLean/GoCore/RecoveryAllocation.lean	[4f7aedef]
GoLean/GoCore/RecoveryCallControl.lean	[f160d7ca]
GoLean/GoCore/RecoveryCallEntry.lean	[63769964]
GoLean/GoCore/RecoveryCallLayout.lean	[10cd6e8f]
GoLean/GoCore/RecoveryCalls.lean	[e8a665e9]
GoLean/GoCore/RecoveryChoices.lean	[10cd6e8f]
GoLean/GoCore/RecoveryContext.lean	[4f7aedef]
GoLean/GoCore/RecoveryControl.lean	[f160d7ca]
GoLean/GoCore/RecoveryControlData.lean	[f160d7ca]
GoLean/GoCore/RecoveryControlHelpers.lean	[f160d7ca]
GoLean/GoCore/RecoveryControlMono.lean	[f160d7ca]
GoLean/GoCore/RecoveryControlTyping.lean	[4f7aedef]
GoLean/GoCore/RecoveryDelivery.lean	[f160d7ca]
GoLean/GoCore/RecoveryDiagnostics.lean	[e8a665e9]
GoLean/GoCore/RecoveryEnvironment.lean	[4f7aedef]
GoLean/GoCore/RecoveryExpressionProgress.lean	[f160d7ca]
GoLean/GoCore/RecoveryExpressions.lean	[e8a665e9]
GoLean/GoCore/RecoveryFrameProgress.lean	[f160d7ca]
GoLean/GoCore/RecoveryGraph.lean	[e8a665e9]
GoLean/GoCore/RecoveryInitialization.lean	[63769964]
GoLean/GoCore/RecoveryInvariant.lean	[f160d7ca]
GoLean/GoCore/RecoveryObservation.lean	[04109912]
GoLean/GoCore/RecoveryOperators.lean	[4f7aedef]
GoLean/GoCore/RecoveryPanicProgress.lean	[f160d7ca]
GoLean/GoCore/RecoveryPool.lean	[10cd6e8f]
GoLean/GoCore/RecoveryPoolObservation.lean	[04109912]
GoLean/GoCore/RecoveryProgramObservation.lean	[04109912]
GoLean/GoCore/RecoveryResultRoots.lean	[63769964]
GoLean/GoCore/RecoverySetup.lean	[63769964]
GoLean/GoCore/RecoverySetupReadout.lean	[63769964]
GoLean/GoCore/RecoverySetupShape.lean	[63769964]
GoLean/GoCore/RecoverySetupWf.lean	[63769964]
GoLean/GoCore/RecoverySingleton.lean	[10cd6e8f]
GoLean/GoCore/RecoveryStatementProgress.lean	[f160d7ca]
GoLean/GoCore/RecoveryStatements.lean	[e8a665e9]
GoLean/GoCore/RecoveryStore.lean	[4f7aedef]
GoLean/GoCore/RecoverySuccessfulRuns.lean	[f160d7ca]
GoLean/GoCore/RecoveryTypingCore.lean	[e8a665e9]
GoLean/GoCore/RecoveryValueBasic.lean	[f160d7ca]
GoLean/GoCore/RecoveryValueCalls.lean	[f160d7ca]
GoLean/GoCore/RecoveryWalk.lean	[f160d7ca]
GoLean/Interface.lean	[7bd32ad6,819182b5,b3d6fa6e,30b09c08,77f154e0,26f0dc09,354ef7f2,f251abcb]	H:L3
Tests/AbortObservation.lean	[04109912]
Tests/AbortObservationAudit.lean	[04109912]
Tests/BooleanInvariant.lean	[8717b974]
Tests/BooleanProgram.lean	[26f0dc09]
Tests/BooleanRuntime.lean	[354ef7f2,f251abcb]
Tests/BooleanSafetyAudit.lean	[26f0dc09,8717b974]
Tests/BooleanTyping.lean	[c7a439f7]
Tests/BooleanTypingAudit.lean	[c7a439f7]
Tests/BooleanTypingFixture.lean	[c7a439f7]
Tests/InterfaceAudit.lean	[7bd32ad6,819182b5,b3d6fa6e,30b09c08,77f154e0,26f0dc09,82e177c7,354ef7f2,ff7173dd,f251abcb]	H:L3
Tests/RecoveryA2Artifact.lean	[e8a665e9]
Tests/RecoveryControlAudit.lean	[f160d7ca]
Tests/RecoveryDiagnosticControls.lean	[e8a665e9]
Tests/RecoveryInvariant.lean	[f160d7ca]
Tests/RecoverySetup.lean	[63769964]
Tests/RecoverySetupAudit.lean	[63769964]
Tests/RecoveryStorage.lean	[4f7aedef]
Tests/RecoveryStorageAudit.lean	[4f7aedef]
Tests/RecoveryTyping.lean	[e8a665e9]
Tests/RecoveryTypingAudit.lean	[e8a665e9]
Tests/RecoveryTypingFixture.lean	[e8a665e9]
Tests/boolean-typing-fixture/main.go	[c7a439f7]
Tests/boolean-typing-fixture/manifest.tsv	[c7a439f7]
Tests/recovery-typing-fixture/main.go	[e8a665e9]
Tests/recovery-typing-fixture/manifest.tsv	[e8a665e9]
docs/2026-09-05_boolean-runtime-contract-design.md	[f251abcb,c53bb6a7]
docs/2026-09-05_boolean-typing-design.md	[c7a439f7]
docs/2026-09-05_typed-contract-design-review.md	[ff7173dd,71183a62,ce896516,d3ffb32b]	H:L3
docs/2026-09-06_abort-observation-contract.md	[04109912]
docs/2026-09-06_abort-observation-independent-review.md	[53ca910a]
docs/2026-09-06_b7-context-store-design.md	[45ff4ae2]
docs/2026-09-06_boolean-initialization.md	[354ef7f2]
docs/2026-09-06_boolean-program-contract.md	[26f0dc09]
docs/2026-09-06_boolean-runtime-invariant.md	[8717b974]
docs/2026-09-06_boolean-storage-setup.md	[f251abcb]
docs/2026-09-06_recovery-control-contract.md	[b3d6fa6e,f160d7ca]
docs/2026-09-06_recovery-entry-contract.md	[30b09c08,63769964]
docs/2026-09-06_recovery-facade-customer.md	[7bd32ad6]
docs/2026-09-06_recovery-facade-migration.md	[7bd32ad6]
docs/2026-09-06_recovery-runtime-design.md	[f160d7ca,4f7aedef]
docs/2026-09-06_recovery-static-claims.md	[e8a665e9]
docs/2026-09-06_recovery-static-design.md	[e8a665e9]
docs/2026-09-06_shared-recovery-customer.md	[10cd6e8f]
lakefile.toml	[7edc298f,39235f65,7bd32ad6,c969079a,b9136a05,819182b5,2a70246f,0ff12435,04109912,f160d7ca,63769964,4f7aedef,212842a9,e8a665e9,26f0dc09,82e177c7,ff7173dd,8717b974,f251abcb,c7a439f7]	H:L3
scripts/check-abort-observation	[04109912]
scripts/check-boolean-runtime	[26f0dc09,8717b974]
scripts/check-boolean-typing	[c7a439f7]
scripts/check-interface	[7bd32ad6,819182b5,b3d6fa6e,30b09c08,77f154e0,26f0dc09,82e177c7,354ef7f2,ff7173dd,f251abcb]	H:L3
scripts/check-interface.py	[7bd32ad6,819182b5,b3d6fa6e,30b09c08,77f154e0,26f0dc09,82e177c7,354ef7f2,ff7173dd,f251abcb]	H:L3
scripts/check-recovery-control	[f160d7ca]
scripts/check-recovery-setup	[63769964]
scripts/check-recovery-storage	[4f7aedef]
scripts/check-recovery-typing	[e8a665e9]
spikes/gate-a1/GateA1/Audit.lean	[f251abcb]
spikes/iris-customer/GoLeanIris.lean	[7bd32ad6,10cd6e8f]
spikes/iris-customer/GoLeanIris/Admission.lean	[7bd32ad6,10cd6e8f]
spikes/iris-customer/GoLeanIris/Allocation.lean	[10cd6e8f]
spikes/iris-customer/GoLeanIris/Audit.lean	[7bd32ad6,10cd6e8f,f251abcb]
spikes/iris-customer/GoLeanIris/Call.lean	[7bd32ad6,10cd6e8f]
spikes/iris-customer/GoLeanIris/Driver.lean	[10cd6e8f]
spikes/iris-customer/GoLeanIris/Examples.lean	[10cd6e8f]
spikes/iris-customer/GoLeanIris/OwnershipTests.lean	[10cd6e8f]
spikes/iris-customer/GoLeanIris/Program.lean	[7bd32ad6]
spikes/iris-customer/GoLeanIris/Readout.lean	[7bd32ad6,10cd6e8f]
spikes/iris-customer/GoLeanIris/Return.lean	[10cd6e8f]
spikes/iris-customer/GoLeanIris/Shared.lean	[10cd6e8f]
spikes/iris-customer/GoLeanIris/SharedDrain.lean	[10cd6e8f]
spikes/iris-customer/GoLeanIris/SharedDriver.lean	[10cd6e8f]
spikes/iris-customer/GoLeanIris/SharedHelpers.lean	[10cd6e8f]
spikes/iris-customer/GoLeanIris/SharedProgram.lean	[10cd6e8f]
spikes/iris-customer/GoLeanIris/SharedReadout.lean	[10cd6e8f]
spikes/iris-customer/GoLeanIris/SharedRecovery.lean	[10cd6e8f]
spikes/iris-customer/GoLeanIris/Terminal.lean	[7bd32ad6]
spikes/iris-customer/GoLeanIris/Unwind.lean	[7bd32ad6,10cd6e8f]
spikes/iris-customer/check	[7bd32ad6,10cd6e8f]
spikes/iris-customer/gate_checks.py	[7bd32ad6,10cd6e8f]
spikes/iris-customer/tools/check_artifact.lean	[10cd6e8f]
tools/abort-observation-audit.py	[04109912]
tools/boolean-runtime-audit.py	[26f0dc09,8717b974]
tools/boolean-typing-audit.py	[c7a439f7]
tools/check-boolean-typing-artifact.lean	[c7a439f7]
tools/check-recovery-fixture-controls.py	[e8a665e9]
tools/check-recovery-typing-artifact.lean	[e8a665e9]
tools/recovery-control-audit.py	[f160d7ca]
tools/recovery-setup-audit.py	[30b09c08,63769964]
tools/recovery-storage-audit.py	[4f7aedef]
tools/recovery-typing-audit.py	[e8a665e9]
```

### L1b (I1 declaration wire, sub-chunk of L1) — 19 paths

```
GoLean/GoCore/Declaration.lean	[0ff12435]
GoLean/NativeDeclaration.lean	[b9136a05,0ff12435]
GoLean/StrictJsonParse.lean	[b9136a05]
Tests/DeclarationAudit.lean	[b9136a05,0ff12435]
Tests/DeclarationWire.lean	[b9136a05,0ff12435]
Tests/StrictJsonParse.lean	[b9136a05]
docs/2026-09-06_i1-admission-design.md	[f3913e06]
docs/2026-09-06_i1-declaration-wire.md	[298e4da1]
docs/2026-09-06_i1-json-boundary.md	[b9136a05]
docs/2026-09-06_i1-positive-declarations.md	[0ff12435]
scripts/check-declarations	[b9136a05,0ff12435]
spikes/i1-declarations/Prototype.lean	[8ea5a74b]
spikes/i1-declarations/README.md	[8ea5a74b]
tools/check-declaration-wire.lean	[0ff12435]
tools/declaration-audit.py	[b9136a05,0ff12435]
tools/lowerdiag/unclassified-formats.txt	[298e4da1]
tools/nativefrontend/declaration.go	[298e4da1]
tools/nativefrontend/declaration_fixture_test.go	[0ff12435]
tools/nativefrontend/declaration_test.go	[298e4da1]
```

### L1-T (recovery-terminal slice; lands with/after L3 — §2.2) — 7 paths

```
GoLean/GoCore/RecoveryPoolObservationTyped.lean	[7bd32ad6]
GoLean/GoCore/RecoveryTerminal.lean	[7bd32ad6]
Tests/RecoveryTerminal.lean	[7bd32ad6]
Tests/RecoveryTerminalAudit.lean	[7bd32ad6]
docs/2026-09-06_recovery-terminal-contract.md	[7bd32ad6]
scripts/check-recovery-terminal	[7bd32ad6]
tools/recovery-terminal-audit.py	[7bd32ad6]
```

### L3 `land/panic-text-tape` — 45 paths

```
Corpus/controls/string-members/explicit/controls.go	[819182b5]
Corpus/controls/string-members/explicit/main.go	[819182b5]
Corpus/controls/string-members/historical/controls.go	[819182b5]
Corpus/controls/string-members/historical/main.go	[819182b5]
Corpus/controls/string-members/historical/subjects.go	[819182b5]
Corpus/coverage/exec/panic-recover/panic-text/cases.tsv	[ff7173dd]
Corpus/coverage/exec/panic-recover/panic-text/main.go	[ff7173dd]
Corpus/coverage/exec/panic-recover/repanic-same-value-abort/cases.tsv	[819182b5]
Corpus/coverage/exec/panic-recover/repanic-same-value-abort/main.go	[819182b5]
Corpus/coverage/exec/panic-recover/string-members/cases.tsv	[819182b5]
Corpus/coverage/exec/panic-recover/string-members/main.go	[819182b5]
GoLean/CLI.lean	[819182b5]
GoLean/GoCore/Machine.lean	[819182b5,ff7173dd]
GoLean/GoCore/Ops.lean	[ff7173dd]
GoLean/GoCore/PanicText.lean	[819182b5]
GoLean/GoCore/StringPanic.lean	[819182b5]
Tests/InterfaceContract.lean	[ff7173dd]
Tests/PanicRendering.lean	[819182b5,ff7173dd]
Tests/StringPanicMembers.lean	[819182b5]
baselines/string-members/panic-recover/repanic-same-value-abort.json	[7edc298f,39235f65,7bd32ad6,c969079a,819182b5]
baselines/string-members/panic-recover/string-members/controls.json	[7edc298f,39235f65,7bd32ad6,c969079a,819182b5]
baselines/string-members/panic-recover/string-members/equal.json	[7edc298f,39235f65,7bd32ad6,c969079a,819182b5]
baselines/string-members/panic-recover/string-members/invalid-after-lf.json	[7edc298f,39235f65,7bd32ad6,c969079a,819182b5]
baselines/string-members/panic-recover/string-members/invalid-before-lf.json	[7edc298f,39235f65,7bd32ad6,c969079a,819182b5]
baselines/string-members/panic-recover/string-members/invalid-recovered.json	[7edc298f,39235f65,7bd32ad6,c969079a,819182b5]
baselines/string-members/panic-recover/string-members/multiple.json	[7edc298f,39235f65,7bd32ad6,c969079a,819182b5]
baselines/string-members/panic-recover/string-members/unequal.json	[7edc298f,39235f65,7bd32ad6,c969079a,819182b5]
baselines/string-members/panic-recover/string-members/unicode.json	[7edc298f,39235f65,7bd32ad6,c969079a,819182b5]
docs/2026-09-06_historical-string-member-argument.md	[819182b5]
docs/2026-09-06_panic-rendering-repair.md	[ff7173dd]
docs/2026-09-06_string-member-certificate-design-review.md	[563c01de]
docs/2026-09-06_string-member-certificate-design.md	[819182b5]
docs/2026-09-06_string-member-claims.md	[819182b5]
docs/2026-09-06_string-member-design-review.md	[4a8a8ad1]
docs/2026-09-06_string-member-fixture-argument.md	[819182b5]
docs/2026-09-06_string-member-production-review-request.md	[819182b5]
docs/2026-09-06_string-panic-member-assessment.md	[b5dd4076]
docs/2026-09-06_string-panic-member-implementation.md	[819182b5]
scripts/check-string-members.py	[819182b5]
scripts/coverage-baseline-diff	[819182b5]
scripts/coverage-manifest	[819182b5]
tools/check_string_member_fixtures.py	[819182b5]
tools/string_member.py	[819182b5]
tools/string_member_runner.py	[819182b5]
tools/test_string_member.py	[819182b5]
```

### L4 `land/observer-terminal` — 5 paths

```
Corpus/coverage/exec/panic-recover/panic-controls/cases.tsv	[d0dbd469]
Corpus/coverage/exec/panic-recover/panic-controls/main.go	[d0dbd469]
Corpus/coverage/exec/panic-recover/panic-markers/cases.tsv	[b5dd4076]
Corpus/coverage/exec/panic-recover/panic-markers/main.go	[b5dd4076]
docs/2026-09-06_observer-controls-repair.md	[d0dbd469]
```

### L6 `land/sprint-records` — 5 paths

```
AGENTS.md	[10fefeb3]
CLAUDE.md	[10fefeb3]
docs/2026-09-05_master-plan.md	[f251abcb,10fefeb3,5a4aca9e]
docs/2026-09-05_typed-consumer-sprint-charter.md	[10fefeb3,5a4aca9e]
docs/2026-09-05_typed-consumer-sprint-handoff.md	[7edc298f,39235f65,c969079a,b34cee67,2a70246f,414a2abe,563c01de,b3d6fa6e,30b09c08,123fd48e,77f154e0,26f0dc09,82e177c7,354ef7f2,f251abcb,c53bb6a7,10fefeb3]
```

### Not landed — `docs/evidence/**`: 2,159 paths (inventoried by L6's MANIFEST.tsv; bytes on the archive branch)


## Appendix B — gc `printpanics` at the pin (for §2.3(b))

`deps/go/src/runtime/panic.go` @ `c19862e5f8` (go1.26.5), read 2026-09-07:

- `preprintpanics` (702–730): walks the chain; `if p.link != nil &&
  *efaceOf(&p.link.arg) == *efaceOf(&p.arg) { p.link.repanicked = true; p =
  p.link; continue }` — eface equality is the type word AND the data word.
  Otherwise `error`/`stringer` payloads are REWRITTEN to `v.Error()` /
  `v.String()` (BUG-004 item 4, unchanged by the sprint).
- `printpanics` (734–755): recurses into `p.link` first (so the OLDEST
  panic prints first — the "first abort line" is the oldest entry);
  `if p.link.repanicked { return }` suppresses the newer duplicate; each
  non-first line is TAB-prefixed unless the link is a `goexit`; prints
  `panic: ` + `printpanicval(p.arg)` + ` [recovered, repanicked]` if
  `p.recovered && p.repanicked`, else ` [recovered]` if `p.recovered`.
- `printPreFatalDeferPanic` (1260–1275): the same identity marking for the
  fatal-during-defer path (BUG-106's shape), without the `Error()`/`String()`
  rewrite.
- Consequence for the machine: the marker is deterministic in the eface
  bits; the eface bits of two equal string payloads are equal iff they are
  the same boxed value — forced when the re-panic passes `recover()`'s
  result through, forced-distinct when either side is a fresh
  `convTstring` allocation of a non-empty string, layout-dependent for two
  independently boxed constants (and the empty string). The machine
  models none of this identity; §2.3(b) reifies the undecided fact as a
  choice and certifies both members with gc witnesses.

## Appendix C — landing-commit message template

```
<chunk>: land <one line>

Squashed from branch typed-consumer-sprint (archive: docs/ARCHIVE.md);
the authored history is on that branch. Built from 7edc298f by path
selection onto main <sha>; hunks of <H files> taken: <list>.

Credits (sprint commits carried): <sha> <subject>, ...
Fixes applied in this chunk: A-Rn ..., B-Rn ... (docs/2026-09-07_typed-sprint-landing-plan.md §2.x)
Excluded: <list> (why)
Gate: scripts/capped scripts/ci --diff at <sha>, jobs=<n>, RESULT: <line>
Baseline: <unchanged | re-pinned NNNN = P / F, reason in header>
Evidence: docs/evidence/<date>_<chunk>/ (<n> files, largest <bytes> B)

[AGENT] <lane>, <date>. Merge on separate [USER] sign-off only.
```
