# Adversarial audit — parking the typed-profile family (`park-lane/typed-profiles-0916`)

**VERDICT: FIX-FIRST — narrow and records-only.** The parking is complete, the
core's machine guard came out STRICTLY STRONGER than the audit it replaced, and
the gate of record at the candidate tip is red in exactly the two expected 5a
places and nowhere else. Three text fixes are owed before merge (F1 README,
F2 a false claim inside a guarding file, F3 the undisclosed gate SHAs); none of
them touches the build, the gate or the trusted surface. If the [USER] drops D7
at the merge ask, F1 self-resolves and the verdict is MERGE-CLEAN.

[AGENT] auditor, branch `review/typed-profiles-parked-0916` @ candidate tip
`bcee0c34` (five commits over main `94da420e`). Ordered by [USER] Mike,
2026-09-16, verbatim, relayed by the [AGENT] coordinator — cite as relayed:
«I agree, we should audit this». I did not merge, push, or edit the candidate
or `main`; I ran no `scripts/ci` (the box-wide lock is the coordinator's).
Evidence: `docs/evidence/2026-09-16_typed-profiles-parked-audit/`.

## Findings

### F1 — INCOMPLETE-DELETION (D7 scope, PENDING [USER]): `README.md` still sends the reader to a deleted spike

`README.md:39` links `[Gate A1 consumer-contract experiment](spikes/gate-a1/README.md)`
and `README.md:43` says «Run its dedicated gate with `bash spikes/gate-a1/check`».
`spikes/gate-a1/` was deleted by `bcee0c34`; `README.md` is untouched anywhere in
the range (`git log --oneline 94da420e..bcee0c34 -- README.md` → empty). A reader
following the top-level README gets `No such file or directory`. No gate catches
it: `git grep -n 'spikes/gate-a1\|spikes/iris-customer' -- ':!docs/'` returns
exactly these two lines and nothing else in the tree.

*Why it matters.* The D7 commit's own claim is that nothing reads the spikes; that
is true of scripts and the lakefile, and false of the repo's front door. A dangling
instruction is the documentation form of a fail-open.

*Disposition (proposed).* If the [USER] ACCEPTS D7: fix `README.md:39-43` in the
same landing (delete the paragraph or re-point it at the tag), in the D7 commit or
a sibling commit so one revert still restores a consistent tree. If the [USER]
DROPS D7: no action. The accept/drop call is the user's; this finding does not
pre-judge it.

### F2 — RECORDS-CLAIM: a false universal inside a core-guarding file

`Tests/GoCoreContract.lean:16`: «Every theorem here is a required export of
`Tests/GoCoreAudit.lean`.» The file declares **36** theorems
(`grep -cE '^(private )?theorem ' Tests/GoCoreContract.lean` → 36); the audit's
`exports` list requires **14** of them (5 §A + 7 §B + 2 §C). Not required, though
compiled: `duplicate_readout_preserves_alias:227`, `nonstring_tail_rejected:335`,
`recovered_transient_rejected:339`, and 19 further §A facts.

*Why it matters.* It is a claim about what the gate enforces, written in the file
the gate guards; a later editor may delete a theorem believing the audit would
notice. The deleted `Tests/InterfaceContract.lean` made no such claim, so this is
new text, not inherited.

*Disposition.* Reword to «14 of the theorems below are required exports of
`Tests/GoCoreAudit.lean`; the rest are compiled by `GoCoreAuditTests`», or add the
missing 22 to `exports`. Records-only; no proof changes.

### F3 — RECORDS-CLAIM: the gate evidence cites commits that are on no branch

`docs/2026-09-16_typed-profiles-parked.md` §3/§6 and
`docs/evidence/2026-09-16_typed-profiles-parked/README.md` attribute the stage-2
and stage-3 gate runs to `421ecc37` and `7ac513e6`. Neither is an ancestor of the
candidate (`git merge-base --is-ancestor 7ac513e6 bcee0c34` → false;
`git branch -a --contains 7ac513e6` → empty): they are the pre-rebase lane
commits, reachable from no ref and therefore garbage-collectable.

I verified the evidence still transfers: `git diff --numstat 7ac513e6 db2de6cf`
and `git diff --numstat 421ecc37 e38b1152` are each exactly
`64 0 docs/2026-08-31_qrow-rulings.md` and
`206 0 docs/2026-09-16_b7-context-store-charter.md` — 2 docs files, 270
insertions, 0 deletions, i.e. precisely what main gained between `62fc8073` and
`94da420e`. **Every Lean, script, tool, `lakefile.toml`, `scripts/ci` and
`ci-libraries.json` byte is identical between the gated commits and the branch
commits**, so the recorded runs are valid for `e38b1152`/`db2de6cf`.

*Disposition.* One sentence in §6 mapping `421ecc37`→`e38b1152` and
`7ac513e6`→`db2de6cf` and stating the 2-docs-only delta. (Honest-measurement rule:
a record a reader cannot resolve from the history is not yet a record.)

### F4 — RECORDS-CLAIM (minor): §1's reverse-import row understates the importers

§1 row 3 says the reverse imports of the family are «`GoLean.lean` (root) only …
plus `spikes/gate-a1` and `spikes/iris-customer`». Recount over every `import`
line under `GoLean/`, `Tests/`, `spikes/`, `Main.lean` at `62fc8073`: **30 files /
33 edges** — the root, 13 spike files, and **16 `Tests/*.lean`**, one of which,
`Tests/PanicRendering.lean`, is a KEPT file that imported the facade. The
substantive claims of that row are true and were verified: no module under
`GoLean/GoCore/` (including the aggregator `GoLean/GoCore.lean`) imports a family
module, and `Main.lean` does not. §3 does disclose PanicRendering's re-target, so
this is a wording gap; a reader of §1 alone could conclude no kept file imported
the facade.

*Disposition.* Add «+ 16 `Tests` modules (15 deleted with the family; the kept
`Tests/PanicRendering.lean` re-targeted in §3)» to the row.

### F5 — SCOPE (PENDING [USER]): `RecoveryPoolObservation` and what left with it

The note's own flag is accurate and I confirm it: `GoLean/GoCore/RecoveryPoolObservation.lean`
at `62fc8073` is 213 lines whose only imports are `GoLean.GoCore.AbortObservation`
and `GoLean.GoCore.ProgramTrace` (no family import); its only importer was the
family's `RecoveryProgramObservation.lean`; it is deleted at the tip. Six required
exports of the OLD audit were its facts or its siblings' —
`stepAbortRecord?_some`, `execPoolWithAbort_erasure`,
`runProgramPoolWithAbortInts_erasure`, `runProgramPoolWithAbort_witness`,
`checkedRunProgramPoolWithAbort_sound`, `Inv.observation_complete/observed_abort`.

I checked the obvious danger and it is absent: the FUNCTIONS those theorems were
about were defined in the same deleted modules, so no kept definition lost its
only theorem. `grep -rn 'execPoolWithAbort\|runProgramPoolWithAbort\|stepAbortRecord?\|PoolAbortWitness'`
over `GoLean Tests tools scripts Main.lean` at the tip returns exactly one hit — a
comment at `Tests/GoCoreContract.lean:318` recording where they went.

*Magnitude, stated honestly (not a defect — D3 authorised it).* The range removes
**548 theorems/lemmas and 128 defs** from `GoLean/GoCore/` and **219 theorems /
82 defs** from `Tests/`. What still constrains the interpreter in-repo: the
trace/run correspondence, `Admission`, the config-level abort observer, the
string-panic members, the panic-text renderer, and the 36 contract regressions.
The typed profiles' preservation/progress/safety statements about `stepFn` are no
longer proved on main; they are recoverable, blob-exact, from the tag.

*Disposition.* PENDING [USER]: reviving `RecoveryPoolObservation` under a core
name is a separate call, as the note says. No action for this landing.

### F6 — NIT: the audit cannot see `@[implemented_by]`/`unsafe` (unchanged, covered elsewhere)

My third independent poison — `unsafe def` + `@[implemented_by]` appended to
`GoLean/GoCore/PanicText.lean` — compiled and the audit returned **EXIT=0** (not
refused). Expected: `collectAxioms` is blind to compiler-level divergence. The
cover is `scripts/ci` step 1a2 («meta-layer escape hatches»), whose scan block
(lines 212-320) is byte-identical between `62fc8073` and the tip and whose file set
is `find GoLean GoLean.lean Main.lean`, i.e. it does cover `PanicText.lean`, with
`META_HATCH_ALLOW=''`. The deleted `check-interface.py` had exactly the same blind
spot. **No regression**; recorded so the division of labour is on the record.

### F7 — NIT: two residual coverage edges of the new harness

(a) `tools/core-audit.py:16-18` globs `GoLean/*.lean` and `GoLean/GoCore/*.lean`
only. A future `GoLean/<subdir>/X.lean` would be audited only if it reaches the
closure (then it fails closed by name, `Tests/GoCoreAudit.lean:126`); an orphan in
a new subdirectory would be silently unaudited. Today `GoCore` is the only
subdirectory, so the hole is theoretical — and the old fixed-list audit was
strictly worse. Cheap fix: `rglob("*.lean")`.
(b) `Tests/*.lean` are audited for axioms (they are in the closure) but are outside
the `scripts/ci` text scans' file set; likewise `Main.lean` is text-scanned but not
in the audit closure. Both were true at `62fc8073`. Suspicion-free statement of
scope, not a finding against the lane.

## (a) Is the core audit weaker than the deleted interface audit? No — it is stronger.

Method: every one of the OLD 110 required exports was resolved to its DECLARING
file at `62fc8073` by a namespace-tracking parser (evidence
`export-coverage.txt`), then classified by whether that file survives at `bcee0c34`.

| Property | DELETED `check-interface.py` + `Tests/InterfaceAudit.lean` (`62fc8073`) | RE-HOMED `tools/core-audit.py` + `Tests/GoCoreAudit.lean` (`bcee0c34`) | Verdict |
|---|---|---|---|
| Required exports | 110 | 51 | — |
| … of which are facts of modules that SURVIVE | **18** core facts + **5** `GoLean.GateA1.*` contract facts | **all 23 still required** (the 5 renamed `GoLean.GoCore.ContractTests.*`) | **0 dropped** |
| … the other 87 | theorems whose DEFINITIONS left with the family | n/a — nothing dangles (verified: no kept file names the deleted functions) | equal |
| New core requirements | — | +28 (`StringPanic` members ×7, `AbortObservation` string-panic/abortRecord ×5, §B interpreter ×7, §C observer ×2, `PanicRendering` ×3, `StringPanicMembers` ×4) | **stronger** |
| Module closure | FIXED list of 66 module names in the source | EVERY `GoLean/*.lean` + `GoLean/GoCore/*.lean` **read from disk**, TWO-WAY (`GoCoreAudit.lean:121-126`): on-disk∉closure and closure∉on-disk both refuse | **stronger** |
| Modules actually audited | excluded `GoLean.CLI` and `GoLean.NativeToIR` by design («forbidden customer dependency») | includes them: 43 modules, 34 under `GoCore`, 15,272 declarations | **stronger** |
| Vacuity guard | none | empty `GoCore` → `RuntimeError` (probed: REFUSED); empty on-disk list → `throwError` | **stronger** |
| Axiom allowlist | `propext`, `Classical.choice`, `Quot.sound` | identical trio (`GoCoreAudit.lean:138`) | equal |
| Constructive helpers | 5 abort-text helpers, `propext`/`Quot.sound` only | same 5, same rule (`:104-107`) | equal |
| Foreign root check | `Iris`/`GateA1`/`GoLeanIris` roots + CLI/NativeToIR forbidden | allowlist `Init/Std/Lean/GoLean/Tests`; any other root refused by name (`:116-117`) | equal-or-stronger (purpose changed with the facade) |
| Compiled poison controls | 3 (`Trace` axiom, facade axiom, audit `sorry`) | 5 (`Trace`, `AbortObservation`, `StringPanic`, the audit itself, contract `sorry`) — all rejected BY NAME in my run | **stronger** |
| Scratch discipline | retained on success (R7 debt) | invocation-owned, removed on success, retained on failure | **stronger** |
| Step fails closed | `bad` on failure | identical `if library_step … ; then ok; else bad` shape; `bad()` still sets `fail=1`; arg guard EXIT=2 (probed) | equal |

Adversarial poisons of my own (`auditor-poison.py`, both in modules the lane did
NOT list as controls): `native_decide` in `GoLean/GoCore/StateWf.lean` →
**REFUSED BY NAME** (exit 1, «depends on forbidden axiom
…auditorNativeHole._native.native_decide.ax_1_1»); a private axiom in
`GoLean/ChoiceTrace.lean` → **REFUSED BY NAME**. And the strongest single result:
an untracked module dropped on disk but imported by nothing
(`GoLean/GoCore/ZZAuditorProbe.lean`) takes the harness RED by name — the old
fixed-list audit would have ignored it. Probe removed; tree clean.

## (b) Re-homed tests: byte-identical

- §A vs `62fc8073:Tests/InterfaceContract.lean`: `difflib` over the aligned bodies
  → **3 changed lines**, all the namespace (`end/namespace GoLean.GateA1` →
  `GoLean.GoCore.ContractTests`), plus one blank line. Every statement and proof
  unchanged.
- The 8 §B interpreter facts and the 4 §C observer facts: each extracted from its
  origin file at `62fc8073` and compared — **12/12 identical**
  (`terminal_at_zero_fuel`←`Tests/BooleanProgram.lean`,
  `duplicate_readout_preserves_alias`←`Tests/BooleanRuntime.lean`,
  `actual_scope_restoration`/`actual_new_local_zero`←`Tests/BooleanInvariant.lean`,
  `registration_is_lifo`/`equal_repanic_keeps_history`/`scope_and_zero_execution`←`Tests/RecoveryInvariant.lean`,
  `write_keeps_both_actual_aliases`←`Tests/RecoveryStorage.lean`,
  `complete_chain_bytes_and_flags`/`nonstring_tail_rejected`/`recovered_transient_rejected`←`Tests/AbortObservation.lean`,
  `stringPanicEntries?_map_entry`←`Tests/RecoveryTerminal.lean`). Nothing reworded,
  nothing weakened.
- `Tests/PanicRendering.lean`: `git diff 62fc8073 bcee0c34` shows one hunk — the
  import (`GoLean.Interface` → `GoLean.GoCore.Machine`) and a provenance header.
  No claim changed. `Tests/StringPanicMembers.lean`: diff empty.

## (c) Deletion complete; nothing else left the build

| Check | Result |
|---|---|
| `GoLean/GoCore/*.lean` on disk | **34** |
| … reachable from `Main.lean` by the import graph | **34/34** (also 34/34 from `GoLean.lean`) |
| `GoLean/*.lean` top level | **9**, all 9 reachable from `Main.lean` |
| The 5 formerly facade-only modules | `Trace`, `PoolTrace`, `ProgramTrace`, `AbortObservation`, `StringPanic` all in the closure; `GoLean.lean` imports the latter three directly, the first two come transitively |
| Dangling imports anywhere (`GoLean/`, `Tests/`, `spikes/`, `Main.lean`, `tools/`) | **0** unresolved of 135 `import` lines in 65 files |
| Lake libs removed vs `62fc8073` | exactly the 9 named, all family-only; 1 added (`GoCoreAuditTests`); no `lean_exe` change; `Tests.PanicRendering`/`Tests.StringPanicMembers` kept library ownership |
| ci steps removed | exactly 9 (`semantic interface`, 7 `typed_step`, `typed recovery terminal classification`); 1 added; `scripts/ci` lines 1-497 and 584-EOF byte-identical to `62fc8073` |
| ci error handling / aggregation | `set -uo pipefail`, `ok()`, `bad()`, `library_step()`, the EXIT trap and the final `RESULT:` block all byte-identical; no `\|\| true`, no skip introduced |
| Escape-hatch scans (steps 1/1a2/1a3) | block md5 identical at both revisions; file set still `find GoLean GoLean.lean Main.lean`; vacuity guard intact |
| `scripts/ci-libraries.json` vs `lakefile.toml` | 8 libs ↔ 7 rows, exact both ways, 0 orphans; `python3 tools/ci_libraries.py check` EXIT=0; `selftests` EXIT=0; `library_step` names == registry names |
| Live references to deleted names | **none** outside `README.md` (F1). Comments only: `GoLean/GoCore.lean:20`, `GoLean.lean:6`, `Tests/PanicRendering.lean:4`, `tools/core-audit.py:5`, `Tests/GoCoreContract.lean` origin citations |
| ci-read data files (`docs/BUGS.md`, `SIZE-ALLOWLIST.tsv`, both coverage ledgers, `tools/lowerdiag/causes.tsv`) | 0 family references |
| Trusted-surface paths (`Corpus/`, `baselines/`, `tools/nativefrontend/`, `tools/coverageharness/`, `Main.lean`, `GoLean/GoCore/Machine.lean`, `StepFn.lean`, `NativeToIR.lean`, `CLI.lean`) | range diff **empty** |
| Non-deletion paths in the whole range | 16 (`GoLean.lean`, 2 new `Tests`, `PanicRendering`, the note, `ARCHIVE.md`, 5 evidence files, `lakefile.toml`, `scripts/ci`, `ci-libraries.json`, `scripts/check-core-audit`, `tools/core-audit.py`) |

## (d) D7

`bcee0c34` is 51 deletions (`spikes/gate-a1` 16 files / 512 lines;
`spikes/iris-customer` 35 files / 2,880 lines) plus 2 doc modifications (the note
§5 sentence and the ARCHIVE clause that name them) — so a revert removes the
claim along with the deletion, which is right. No script, tool, lakefile or
manifest reads `spikes/` (`git grep -nI 'spikes' -- scripts tools lakefile.toml
lake-manifest.json` → empty); no earlier commit in the range touches `spikes/`.
Revert dry-run: `git diff bcee0c34 bcee0c34^ | git apply --check` → **EXIT=0**
(clean, in isolation, no working-tree mutation). Both dirs are present and
blob-exact at the tag. `spikes/i1-declarations` is untouched, as §4 says.

## (e) Records

Every recountable number in the note, the ARCHIVE entry, the evidence README and
the five commit messages is **exact**: 57/8,382 (56/8,197 + 185); 24/3,043; 224
re-homed; 2 fixture dirs/4 files; 106 paths/12,293 lines at `db2de6cf`; 16/512 and
35/2,880 at `bcee0c34`; 9 libraries / 9 ci steps / 9 registry rows / 10 scripts /
11 tools, each list exact; 10 core modules the family imported; 5 facade-only
modules; 13 spike importers; `RecoveryPoolObservation` 213 lines; 34 remaining
`GoCore` modules; 17 Tests modules / 7 steps; drift 331 = 330 (325/4/1) + 1;
8 vs 7 red steps; the one-step/one-row `comm`.

Preservation: the tag `typed-profiles/last-main-2026-09-16` is annotated
(`^{commit}` → `62fc80731f0045c170634690bda1c26d1880f185`), equals branch
`park/typed-profiles-2026-09-16` and the note's SHA; **all 157 paths deleted in
the range exist in that tree and every one is blob-identical to its `94da420e`
version** — the revive command in §2 is exact. Evidence dir 36 KiB, largest file
27 KiB, both caps clear; `scripts/check-evidence-size` EXIT=0 including my own
evidence. Adjacent candidates (§4) all present and byte-untouched by the range
(`AdmissionTests`, `DeclarationTests`, `MethodIdentity*`, `UnseqScheduler*`,
`EvalTests`' `Tests/GoCoreEval.lean`, `GoLean/GoCore/Admission*.lean`,
`spikes/i1-declarations`, `tools/typed_audit.py`,
`scripts/typed-gate-scratch.sh`); the note's §4 list names «`Tests/Eval*.lean`»,
which does not exist — the module is `Tests/GoCoreEval.lean` (NIT, subsumed by F4's
class). Records gaps: F2, F3, F4.

## (f) Build and the gate of record

`scripts/setup-deps --from /home/dev/projects/golean` EXIT=0 (goose `3be88bb`,
raft `56e3200`, go `c19862e5f8`). `.lake` warmed by a plain `cp -a`;
`scripts/capped lake build` **EXIT=0** (92 jobs). All seven libraries
`scripts/capped lake build GoCoreAuditTests TestsData EvalTests AdmissionTests
DeclarationTests MethodIdentityTests UnseqSchedulerTests` **EXIT=0** (68 jobs).
There is no `GoCoreContractTests` library — `Tests.GoCoreContract` is globbed by
`GoCoreAuditTests` (`lakefile.toml:54-55`), matching the registry.
`scripts/capped scripts/check-core-audit` **EXIT=0**: 43 modules (34 under
`GoCore`), 51 required theorems, 15,272 declarations, classical trio only, 5
controls rejected by name, scratch removed.

The coordinator's gate of record at `bcee0c34` with `deps/` present COMPLETED
while I worked (`.tmp/ci-record.exit` = `1`). Red steps: **exactly two** —
`certificate provenance` («STALE certification: changed dependency
build/files/GoLean.lean») and `baseline diff`, whose drift block is **exactly one
row**, `imported-goose/channel/google-search baseline[PASS/membership] ->
now[FAIL/membership]`. `differential coverage summary: cases=3676 pass=3427
fail=249` against the baseline's 3428/248 — one row moved. **That is precisely
the expected 5a pair and nothing else**; the six environmental reds of the lane's
own no-network run are gone now that `deps/` is present, which retires the lane's
control-based argument in favour of a direct measurement. The staleness is
structural and correctly NOT re-pinned in-lane: the certified record's
`inputs.build.files` map lists every `GoLean/**` file (including the 56 deleted
modules) plus 21 deleted `scripts/`+`tools/` paths, and `GoLean.lean`'s hash
changed — `baselines/` is untouched by the range. **Step 5a re-certification is
owed at the merge train**, per the charter.

## What I did NOT check

- I did not run `scripts/ci` (the lock is the coordinator's); I report its log,
  I did not reproduce it. I did not re-run the differential corpus, re-derive any
  baseline, or verify the 249 failing rows individually.
- I did not verify that the 87 dropped required exports were *semantically*
  redundant — only that their definitions left with the family and that nothing
  kept refers to them. Whether the typed profiles should have been parked at all
  is the [USER]'s D3 ruling, not an audit question.
- I did not audit the CONTENT of the deleted modules for anything worth rescuing
  beyond the note's own list; F5 flags the one module (`RecoveryPoolObservation`)
  whose imports were core-only.
- I did not test the audit against a poisoned `Tests/*` module other than the
  lane's own `contract_trailing` control, nor against `opaque`, nor a tampered
  `.olean` on `LEAN_PATH` (the overlay mechanism itself is the lane's, inherited
  from the reviewed 2026-09-08 driver; I used it rather than re-reviewing it).
- I did not check `raftsubject/`/`raftharness/` or the frontend beyond confirming
  the range does not touch them.
- Spike content (what `spikes/gate-a1` and `spikes/iris-customer` proved) was not
  reviewed; D7 is a scope call for the [USER].
- Disclosure: a delegated read-only sweep read the lane worktree's gitignored
  `.tmp/ci.log`/`ci-base.log` in addition to the gate-of-record log my brief
  named. Nothing there was modified; the readings agree with the tracked evidence.

## Proposed dispositions (all PENDING [USER] where marked)

1. F1 — fix `README.md:39-43` in this landing **if D7 is accepted** (PENDING [USER]).
2. F2 — reword `Tests/GoCoreContract.lean:16`.
3. F3 — one sentence in the note §6 mapping the pre-rebase gate SHAs.
4. F4 — widen §1's reverse-import row.
5. F5 — `RecoveryPoolObservation` revival is a separate call (PENDING [USER]).
6. F6/F7 — no action; recorded scope.
7. Merge train: step 5a re-certification is owed (expected, structural).
