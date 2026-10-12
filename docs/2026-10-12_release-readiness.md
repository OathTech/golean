# Release readiness — the punch list (2026-10-12)

[AGENT] coordinator, from the independent Fable review of `main` @ `d92b95fd` (read-only; the fast tier
PASS at 65 s; twelve declared-unsupported constructs probed end to end, every one refused by name; the
fail-open arms of the decoder, the CLI, the core and the frontend read; every open `BUGS.md` entry
classified). Authority: [USER] Mike 2026-10-12: «assess the project for release readiness … (1)
well-documented, (2) unsupported features should be fail-closed, all known bugs should be fixed, should
trigger warnings, or should be blocked, (3) any built up debt should be identified and targeted for
resolution, and (4) there should be clear top-level documentation of the project and how it can be used»;
then «write the whole punch list and then you can manage some agents working through the backlog, starting
with the ones that require no input from me». Rulings so far: **LICENSE holder: Oath Technologies, 2026**
([USER], same day).

This file is the BACKLOG: each item carries a status, updated as lanes land (`OPEN`, `LANE <name>`,
`DONE <commit>`, `NEEDS [USER]`). Dispositions and evidence are the reviewer's; [V] = verified by reading
the code, row or output, [I] = inferred from records.

## 0. Verdict

The semantics is in good shape: the core is total (no `sorry`/axiom/`native_decide`; zero `partial` in
`GoLean/GoCore/`), the differential is green at 3936 rows with every red rowed, the coherence statements
are pinned in `BridgeSet.lean`, and every unsupported construct probed refused by name. The product is not
release-ready: records and packaging mostly, plus a short list of genuine defects (three open behaviours
that give a plausible wrong value with no marker; one fail-open arm in the decoder and the frontend; an
unfilled LICENSE; entry points that disagree on the plan of record; no wire or observation format
specification; no definition of a release).

**What a release is** ([AGENT] proposal, PENDING [USER]): the 2026-10-03 re-pin offer, generalised and
public — a tagged commit `release/<date>`; the pinned toolchains (Lean `v4.32.2`, `go1.26.5`);
`scripts/ci --diff` green with the tracked baselines at the tag; a changelog frozen from the previous
release tag; a stated-limits section (the offer's ten limits are the template); and the three release
predicates of `docs/2026-09-05_master-plan.md` §7.3 reported separately — no unclassified failures; zero
known wrong answers within a NAMED supported profile; a stated envelope.

**Distance:** the blocking items are one to two sessions of fixes plus two to three sessions of
documentation. The «zero known wrong answers» predicate is reachable only by fixing or guarding
BUG-061/099/121, or by naming a supported profile that excludes them — a [USER] call pending since
2026-09-05.

## 1. Punch list

### Release-BLOCKING

| # | crit. | item | evidence | fix (size) | status |
|---|---|---|---|---|---|
| 1 | 2 | **Three silently-wrong behaviours are open.** BUG-061: `multipkg/init-order-staticinit/seq` Lean `21`, Go `12`, both `ok`. BUG-099: `panic-recover/recovered-runtime-error-type/observed` machine `{"dynamic":"Error", string}` vs gc `boundsError`, `ok` (three sibling rows refuse by name). BUG-121: `[]byte(s)` zero-copy aliasing (gc `&b[0]==&c[0]` TRUE, machine FALSE; `Machine.lean:773` always fresh-allocates) has NO corpus row; its cited evidence was deleted by the evidence triage. `check-bugs`'s «wrong-answer 0/0» is true by accounting, not behaviour. | [V] `artifacts/coverage/latest.tsv`; BUGS.md entries | pin BUG-121 with a membership row (1 h); guard BUG-099's `observed` shape by name or fix (a session); BUG-061 fix or ratify as latitude L-011 with an envelope row (a session+); OR name the supported profile that excludes them | BUG-121 row + BUG-099 guard: LANE `fix/release-runtime-1012`; BUG-061 and the profile: **NEEDS [USER]** |
| 2 | 2 | **One genuine fail-open arm, on both sides of the wire.** `GoLean/NativeToIR.lean:1010-1015` `exprTypeOf`: `\| none => pure (.int .int)` when a node has no `type` (callers :2318, :2342 range temp; :2663, :2671 discard temps). `tools/nativefrontend/emit.go:5366-5370` drops the `type` key silently when `typeOf` errors. A temp declared `int` holding a non-int value: `StateWf`'s declared-type invariant is fed a lie — the class BUG-043/BUG-110 retired elsewhere. | [V] | refuse by name on a missing key; return the `typeOf` error (hours + `--diff`) | LANE `fix/release-runtime-1012` |
| 3 | 4 | **LICENSE is the unfilled Apache-2.0 template** (`LICENSE:189` «Copyright [yyyy] [name of copyright owner]»); README has no license sentence. | [V] | fill in; one README sentence (hours) | RULED: Oath Technologies, 2026 — DONE on `docs/release-records-1012` (`d9b322c5`), merge pending |
| 4 | 4 | **No definition of «release», no tag scheme, version `0.1.0`, changelog incomplete.** Tags: `logic-offer/2026-10-03`, `typed-profiles/last-main-2026-09-16` only; `docs/changelog/20d3946d-WINDOW.md` stops at train r75: the gate cull (consumer-visible: `--slow` refused by name, `tools/certification.py` and merge step 5a gone) has no row. | [V] | `docs/release.md` (the definition above), a `release/<date>` tag convention, the changelog row (a session) | DONE on `docs/release-records-1012` (`36f5ab8f`: `docs/release.md` PROPOSED, the cull's changelog row), merge pending; the definition itself NEEDS [USER] D2 |
| 5 | 1/4 | **Entry points disagree on the plan of record and point at historical docs.** `README.md:3` and `docs/architecture-rules.md:22` name the master plan; `CLAUDE.md` «Pointers» names the window charter + `docs/2026-09-24_window-plan.md`, whose last status line says «Remaining: unit 7b» (landed 2026-10-03, no closing note); `docs/archive/README.md` calls `TODO.md` and `docs/roadmap.md` «living contracts». README: :12 «the Go-to-Lean tool» (no product statement); :40 «reference dependencies under `../deps`» (does not exist); :88 `scripts/diff-one litmus/if-return` (no such case). | [V] | one README rewrite (what / why / build / run / read a result / add a case / trust / limits) + pointer fixes (a session) | DONE on `docs/release-docs-1012` (`db06db4c`), merge pending — AFTER this backlog lands (README points at it); the CLAUDE.md «Pointers» sentence is proposed in §5 D5 |

### SHOULD

| # | crit. | item | evidence | fix (size) | status |
|---|---|---|---|---|---|
| 6 | 1 | **No wire-format or observation-format specification; CLI help incomplete.** `golean-native-v3` is defined only by `emit.go` + `NativeToIR.lean` and seven dated notes; `golean-observation-v1` (`{"output","schema","status","values":[{"kind","tag","value"}]}`) is in no living doc. `GoLean/CLI.lean:159-167` usage lists three subcommands; `Main.lean` dispatches a fourth, `choice-trace`. | [V] | `docs/cli.md` with both schemas and the fourth subcommand (1–2 sessions) | DONE on `docs/release-docs-1012` (`16140cad`; the decoder declared normative; `choice-trace` in the usage string), merge pending |
| 7 | 1 | **`docs/` is not navigable:** 338 files, 295 dated (Jul 27 / Aug 79 / Sep 165 / Oct 24), 166 banner-marked historical, no index. The living set is ~15 files. | [V] | `docs/README.md` index by role; every dated file a record (a session) | DONE on `docs/release-docs-1012` (`1ce2fa62`), merge pending |
| 8 | 2 | **The negative corpus tests gc's rejections, not GoLean's refusals; the baseline pins a red's stage, not its cause.** `scripts/coverage-negative:170-181` passes a row iff `go build` fails with the expected substring; `coverage-baseline-diff` compares `(result, id, stage)` only, so a changed refusal cause or a crash at the same stage still matches. Gate-audit F9 (2026-09-05), accepted, still open. | [V] | a refusal lane with an expected cause substring, or pin the cause for FAIL rows (1–2 sessions; a baseline-format change — design first) | OPEN — design note first, then a lane |
| 9 | 2 | **Two «fail-closed» stops are crashes.** BUG-090's row `strings/trimspace-repeat/repeat-bound-refused` is `Lean run KILLED (exit 134 … Stack overflow)`, while `docs/BUGS.md:4285` and the row cite a helper `goleanShimStringsRepeatBound` that exists nowhere. BUG-122: `choice-trace --batch` write failures are uncaught IO exceptions (`GoLean/ChoiceTrace.lean:1089-1106`). | [V] | a named budget refusal; catch and name the write failure; correct the records (hours–a session) | LANE `fix/release-runtime-1012` |
| 10 | 2/3 | **BUGS.md hygiene.** 16 open (not 17); BUG-121 and BUG-122 cite evidence deleted by the triage (the triage's train-stamp rule deleted the dirs regardless of living citations — [AGENT] error); BUG-110's heading says «unfixed» with `Status: fixed`; BUG-002 and BUG-065 describe mechanisms that no longer exist; BUG-078 names `TODO.md` as owner; BUG-107 awaits a [USER] ruling posed 2026-09-07; BUG-114's `why` note never applied. | [V] | restore the two cited files from history (`git show 63c9ea65:…`); fix the texts (hours); BUG-107 ruling | DONE on `docs/release-records-1012` (`b0e4179f`: the two files restored, texts fixed, BUG-114's `why` applied), merge pending; BUG-107: **NEEDS [USER]** D3 |
| 11 | 1 | **Semantics documentation for a user of the relation lives in dated notes and docstrings** (`docs/2026-09-24_execution-statement.md`, `docs/2026-09-28_step-label.md`, `docs/2026-10-04_pool-relation-spec.md`, module headers); `docs/semantics.md` still describes the Gobra pipeline; `docs/nondeterminism-design.md:3` says «not yet implemented» for the implemented, pinned choice tape. | [V] | one living «semantics overview» (relation, drivers, `StepLabel`, observation, choice tape + replay, refusal classes, the five endings) pointing at the pinned names (1–2 sessions) | DONE on `docs/release-docs-1012` (`3c142280`: `docs/semantics-overview.md`, every cited name grep-verified), merge pending |
| 12 | 3/4 | **`docs/ARCHIVE.md` is wrong for this clone:** says the parked branches «resolve locally»; none is a local branch, `refs/snapshots/` is empty; six are `origin/*`; `park/typed-profiles-2026-09-16` is not on origin (its tag is). | [V] | rewrite the branch table for the pushed state (hours); the push of the missing branch is the [USER]'s | DONE on `docs/release-records-1012` (`5126df7e`), merge pending; the push: NEEDS [USER] D4 |
| 13 | 2 | **Three deliberate escape hatches are undocumented where a CLI user looks:** `Choices.consume` wraps an out-of-range pick (`c % b`) and yields 0 on exhaustion, `native-json-run` never checks leftover tape (`State.lean:205-209`); `--allow-hidden-dep-init-order` turns a refusal into a stderr warning (`hiddendep.go:261-265`); the frontend exits 0 and emits a stub for a refused declaration (`emit.go:237-295`), so a wire is not a lowering certificate. | [V] | document in `docs/cli.md` (hours; into item 6) | DONE with item 6, merge pending |
| 14 | 4 | **CLAUDE.md's `partial` inventory is incomplete:** 35 `partial def`s outside the core in six files (NativeToIR 17, CLI 7, StrictJsonParse 5, ChoiceTrace 4, NativeDeclaration 1, EnumDedup 1); the charter names three. | [V] | fix the charter sentence (hours) | DONE on `docs/release-records-1012` (`dd5b7060`), merge pending |

### NICE

| # | crit. | item | fix | status |
|---|---|---|---|---|
| 15 | 1 | `docs/2026-10-11_recovery-and-migration-plan.md` §7 still instructs `python3 tools/certification.py release-check` (deleted) | one-line note | DONE on `docs/release-records-1012` (`563a0f1c`), merge pending |
| 16 | 4 | No OS/platform sentence in README; the gc linux/amd64 instance is stated only in CLAUDE.md | one sentence | DONE with item 5, merge pending |
| 17 | 1 | `docs/semantics.md`, `docs/architecture.md`, `docs/roadmap.md` each say «a rewrite is owed (TODO.md)» — TODO.md is historical | fold into item 11 or mark | DONE with item 11 (HISTORICAL banners; `nondeterminism-design.md` marked IMPLEMENTED), merge pending |
| 19 | 2/3 | **Four more BUGS.md evidence citations dangle** after the triage (found by the records lane): `2026-09-11_project-review/probe-results.json`, `2026-09-24_unseq-stage-e6a-audit/…`, `2026-10-07_fr37/ci-slow-run1.tail.txt`, and a truncated `2026-09-24_unseq-…` path. | restore from `63c9ea65` where the citation is load-bearing (a reproduction), else repoint the entry at history (`git show 63c9ea65:…`) | OPEN — a short records lane |
| 20 | 3 | **BUG-078's leftover items have no owner row** now that the entry points at this backlog instead of `TODO.md`. | add the row here with the items from the entry | OPEN — with item 19 |
| 21 | 1 | Stale pointers the docs lane found but did not edit (outside its one code edit): `tools/nativefrontend/main.go`'s header still says `golean-native-v2` and names `GoLean/NativeJson.lean`; `step_complete`'s docstring still says «two nondeterministic step classes». | two comment fixes | OPEN — ride with the next frontend/core lane |
| 22 | 2 | Two CLI shapes documented rather than fixed: a CLI-level `status:error` observation has no `output` key, so `observation-eq` cannot decode it; the `func` value tag is emitted but refused by the decoder. | decide: add the key / refuse the tag at emission (a [USER]-visible schema change — document in `docs/cli.md` meanwhile, done) | OPEN — NEEDS [USER] if the schema moves |
| 18 | 3 | Latitude inventory `file:line` anchors have drifted; nothing checks them since the reconciler was retired | accept as records; a note in the inventory's anchor section | DONE on `docs/release-records-1012` (`3420c905`), merge pending |

## 2. BUGS.md — the open entries, classified

| id | title (short) | class | evidence |
|---|---|---|---|
| BUG-121 | `[]byte(s)` zero-copy aliasing | **silently wrong, UNPINNED** | [V] no corpus row; `Machine.lean:773`; inventory R19 |
| BUG-061 | init schedule under-prunes `staticinit` | **silently wrong** | [V] `multipkg/init-order-staticinit/seq` FAIL/differential, both `ok` |
| BUG-099 | recovered runtime error is one synthetic `$runtime.Error` | **silently wrong (1 row) + blocked by name (3)** | [V] `…/observed` wrong dynamic type, `ok`; `assert-int`, `panic-preprint/*` refuse naming BUG-099 |
| BUG-008 | imported named types' comparability | blocked by name | [V] `Ops.lean:3793` |
| BUG-004 | abort rendering, invalid-UTF-8 first line | blocked by name (both sides) | [V] `crashview.go:128`; `StringPanic.lean:227` |
| BUG-041 | race footprint over-approximation | blocked, cause NOT named | [V] `race/free/array-dyn-index-read-write` reports a generic false race |
| BUG-002 | expression-step atomicity | unclear / entry stale | [I] its listed obligations landed (r70); live residue is inventory U-5 |
| BUG-065 | worker-pool/sum enumeration | blocked by name, mechanism stale | [V] the recorded refusal is the undeclared `backedge` parameter |
| BUG-090 | assoc-list heap cost | **blocked, NOT by name; record wrong** | [V] stack-overflow abort exit 134; cited helper does not exist |
| BUG-093 | print residuals | blocked by name | [V] FR-29 quarantine; `StepFn.lean:1266` |
| BUG-094 | NaN bits | blocked by name | [V] `Ops.lean:203,208`; [a]+[b] deferred by [USER] |
| BUG-100 | local defined type as type argument | blocked by name | [V] `mono.go:1073` |
| BUG-106 | fatal during unwinding | blocked by name (apparatus) | [V] `crashview.go:190` |
| BUG-107 | pre-`main` abort, no crash-channel ack | blocked by name (apparatus); [USER] ruling pending since 2026-09-07 | [V] `crashview.go:74`; 5 rows |
| BUG-114 | observer refuses a second report boundary | blocked by name, intermittent; row PASS | [V] `wake-then-abort` PASS at K=32; `why` note unapplied |
| BUG-122 | `choice-trace --batch` write failure | blocked, NOT by name | [V] `ChoiceTrace.lean:1089-1106` unguarded |

`scripts/check-bugs.sh`: EXIT=0, 122 bugs, untriaged fidelity reds 14 (coverage 10/10, latitude 4/4, wrong-answer 0/0).

## 3. Debt (criterion 3)

| item | where recorded | release-relevant | disposition |
|---|---|---|---|
| Legacy evaluation-order triple (`unseqProbe`/`probeK`/`unseqPanic`) survives; E6b–E6e off the path | changelog 61958f2e limit 3; window plan | yes (customer `cases` arms) | document as limit |
| NaN [a]+[b] envelope (BUG-094) | charter §5; inventory R7 | yes | document as limit (refuses by name) |
| `unseq` commutation theorem (DRF-confluence claim WITHDRAWN) | charter §5; limit 9 | yes for proofs | document as limit |
| NPDRF reduction «explicitly unusable»; access-granularity obligation | CLAUDE.md; inventory §11 item 5; dispositions §3 (restate vs delete PENDING [USER]) | yes (no concurrent claim) | document as limit; pose the ruling |
| Post-window lanes D-6/7 module-path mapping, D-3 `%+#v`, D-12/H-20 writer-typed globals | window plan §4; not in the post-offer changelog | no (raft subject only) | document; schedule |
| Typed profiles PARKED; the reasoning product on `origin/park/reasoning-2026-08-31`; `park/typed-profiles-2026-09-16` not on origin | ARCHIVE.md; `docs/2026-09-16_typed-profiles-parked.md` | no | item 12; the push is the [USER]'s |
| 18 open frontier rows FR-1…FR-35 (refuse by name) | language ledger §4 | yes (scope) | the ledger is the doc; summarise in the release text |
| 18 (b)-PINNED latitude entries with re-envelope obligations; known-≠-oracle E3, E7, R19 (+ E5) | inventory §10, §7 | yes | the envelope statement (predicate 3) |
| (d) UNKNOWN U-2…U-7; U-5 wide ops are single steps | inventory §6 | yes for concurrency | document as limit |
| 4 `latitude` untriaged rows + 10 `coverage` | `baselines/untriaged-ids` | yes | document; R15 lane PENDING [USER] |
| 6 fmt shims (E10 «no injected library text» not met) | stdlib register; master plan §7.3 | yes | document as limit |
| `overlay-import` cap 8 «[AGENT]-provisional pending [USER]» | stdlib register | no | pose for ratification |
| `initPrintRefusal?` retained; setup is a premise; `NoRefusal` sequential-only | CLAUDE.md; limits 6, 7 | yes | already stated; carry into the release text |
| Readout prints raw location ids (`locJson`) | limit 5 | yes | document as a schema limit |
| Platform fixed to `gcAmd64`; no 32-bit oracle | `Platform.lean:84-90`; inventory §11 item 1 | yes | document as limit; a second instance PENDING [USER] |
| 35 `partial def`s outside the core | this review (item 14) | no | fix the charter list |
| Ledger TODO rows T-1…T-8; T-8: 16 concurrent strict rows not confluence-certifiable | language ledger §7 | yes (claim scope) | document as limit |
| `causes.tsv` has an `unrowed` labeled-shape refusal family | `tools/lowerdiag/causes.tsv` | no | add the FR row |
| BUG-107 ruling; BUG-114 `why` note; BUG-110/002/065/078 stale text | BUGS.md | no | item 10 |
| ~15 `PENDING [USER]` markers in living docs (220 overall, the rest in dated records) | grep | partly | triage the living ones; leave the records |
| Gate-cull consumer changelog row missing | `docs/changelog/20d3946d-WINDOW.md` | yes | item 4 |
| `docs/semantics.md`/`architecture.md`/`roadmap.md` rewrite «owed (TODO.md)» | their banners | no | item 17 |
| Negative lane = gc rejection only; cause text not pinned (F9) | gate audit F9; this review | yes | item 8 |

## 4. Verified as already meeting the bar

Fast tier PASS (65 s, EXIT 0); the gate two-tiered with report-only speedbumps and the workflow matching it ·
`GoLean/` free of `sorry`/axiom/`native_decide`; zero `partial` in `GoLean/GoCore/` · every `| _ =>` /
`none =>` arm in `StepFn`, `Ops`, `Machine`, `Multi` throws a named stop; `Stop.status` never yields `ok`;
`native-json-run` exits 1 on every error (~800 arms read, one genuine fail-open: item 2) · twelve declared-
unsupported constructs probed end to end, every one refused naming the construct · the stdlib register =
frontend tables byte for byte · toolchain pins consistent (lean-toolchain, oracle pin, README, spec-sources,
workflow) · every `docs/*.md` link in the entry points resolves · README Getting Started correct post-cull ·
the customer pin verified: `golean-logic`'s `pins.json` `golean.rev` = `20d3946d` = tag `logic-offer/2026-10-03`,
an ancestor of `main` · how to add a corpus case documented (`docs/coverage-suite-structure.md`) · zero
`TODO`/`FIXME`/`HACK` in `GoLean/`, `tools/`, `scripts/` · the evidence tree at 73 dirs / 6.2 MB with a stated bar.

## 5. Decisions for the [USER]

- **D1** The supported-profile ruling behind item 1: fix or guard BUG-061 (and the BUG-099 row), or name the
  profile that excludes them in the release text.
- **D2** The release definition in §0 (proposed; `docs/release.md` is drafted from it in the records lane).
- **D3** BUG-107's ruling (posed 2026-09-07).
- **D4** The push of `park/typed-profiles-2026-09-16` (item 12), or leave it tag-only.
- **D5** The `CLAUDE.md` «Pointers» sentence proposed by the docs lane ([AGENT] wording, a charter edit): «The plan
  of record: the release-readiness backlog `docs/2026-10-12_release-readiness.md` (each item carries its status)
  and the seeded-heap design `docs/2026-10-09_seeded-heap-design.md`; the batched-window charter and its window
  plan closed with the 2026-10-03 offer · The index of living documents: `docs/README.md` · The semantics
  overview: `docs/semantics-overview.md` · The CLI, wire and observation formats: `docs/cli.md`».
- RULED: LICENSE holder Oath Technologies, 2026 (item 3).
