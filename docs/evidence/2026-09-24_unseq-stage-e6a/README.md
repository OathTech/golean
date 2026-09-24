# Evidence — Stage E6a of the evaluation-order model v2.1: the trigger refinement, the non-main-unit grammar, the decoder follow-ups, the status-diverse row (lane `core/unseq-stage-e6a-0924`, 2026-09-24)

[AGENT] worker. Design record `docs/2026-09-24_unseq-stage-e6-design.md` §E6a, handoff
`docs/2026-09-24_unseq-stage-e6a-handoff.md`. Small tables and gate tails only (caps 256 KiB / 4 MiB —
`scripts/check-evidence-size`); bulk runs are reproduced by the commands named per file. Toolchain: go1.26.5 (the pin,
`baselines/go-oracle-pin`); Lean per `lean-toolchain`; host linux/amd64, the shared build box (concurrent lanes; timing numbers
are not load-controlled). Commit: the tree at the branch's tip (the C1/C2/C3 hashes in the handoff §1); the census and probe
files were produced on the working tree before the commits, with the frontend binaries named in each header. Every gate is
capped (`scripts/capped`); the full gates ran under the box-wide lock; captured exits; a killed or timed-out command decided
nothing.

## The measurements

| file | what | producer |
|---|---|---|
| `census-before.txt` | the whole-sweep census with main `3fb4a0d1`'s frontend: 108 258 corpus sweeps, 179 admitted (main units only), the twin 10 203 / 0 | `.tmp/census/run.sh <frontend> <out.tsv>` (Stage E's tooling, copied from the E5 worktree) + `summarize.py` |
| `census-e6a.txt` | the census with the E6a frontend: 265 admitted (`main` 205, `strings` 44, `bytes` 14, `wirepb` 2), the twin 10 203 / 7; the diff vs BEFORE — 93 newly admitted (86 corpus in 41 packages + 7 twin), 0 lost, by former reason («no call occurrence» 48 = the refined trigger; «callee outside the main package» 34; `len` over a map 5; «method callee outside the main package» 3; `pkg.F` 2; `cap` over a channel 1); the twin's legacy reasons after E6a | `run.sh`, `summarize.py`, `diff.py` |
| `census-newly-admitted-e6a.tsv` | the 93 sweeps that enter (package, unit, file:line, function, form, counts, the former reason) | `diff.py` |
| `probes-before.txt` / `probes-e6a.txt` | the LEGACY PROBE EMISSION census (E6's entry metric) — `unseq-probe` / `unseq` nodes per emitted package wire and per function with the probed head: **58 corpus (17 packages) + 128 twin → 47 corpus (17) + 128 twin**; the E6a file lists every remaining emitter, corpus and twin | `.tmp/census/probes.sh <frontend> <out.tsv>` + `probe-sites.py` |
| `trigger-general-footprint.txt` | the GENERAL trigger form's footprint (any two unordered failing occurrences — NOT shipped, POSED: handoff §2 item 1): 179 → 978 admitted (856 newly, 57 twin; `strings` 132, `internal/strconv` 88, `math/bits` 84, …); with E6a's other widenings 179 → 1034 | the same tooling on `.tmp/nativefrontend-e6a-trigger` (main + the general rule) and the first `.tmp/nativefrontend-e6a` build |
| `twin-structural-diff.txt` | the pinned twin wire (e1a87725…) vs the E6a frontend's fresh emit (1c4e7038…): 3 `unseq` graphs born (`raft.isHardStateEqual`, `raft.MustSync`, `raftpb.(*Snapshot).SizeMessage`), 0 entries added / removed, 128 probes unchanged, every other change temp renumbering; the tracked producer's leaf classes | a direct per-entry count (in the file) + `docs/evidence/2026-09-05_fr19-bug097/twin-repin/twin-structural-diff.py` |
| `diff-one-e6a.txt` | `scripts/diff-one` on the 395 rows of the 41 affected packages + the born row's package on the candidate (392 unchanged, 1 born, 2 strict rows RED-FIRST — FAIL/differential, the other spec-legal panic) and the re-run of the 3 rows after the manifests moved (3 PASS/membership); the comparison vs the re-pinned baseline | `.tmp/e6a/diff-one-run.sh <ids> <log>` |
| `gc-draws-e6a.txt` | gc's 20 draws per subject (5 runs × GOMAXPROCS 1/8 × default / `-N -l`) for the born subject, the 10 subjects whose sweeps left the probe and the 2 moved rows' subjects — every subject one member 20/20, inside its set | `.tmp/e6a/gc-draws.sh`, `gc-draws-args.sh` (a subject argument) |
| `gate-exits-e6a.txt` | the standalone gates' captured exits at the tree (go tests, the two wire gates, mem-callsites, core audit, unseq scheduler, frontend pins, bugs, evidence size, spec anchors, agents alias, lane validation) | `.tmp/e6a/gates-small.sh`, `wire-gates.sh`, `wire-gate2.sh` |
| `ci-diff-c1.tail.txt` | the C1 gate's tail (the frontend + twin + rows + baseline; the C2 files stashed): EXIT=1 in 871 s, cases=3761 pass=3524 fail=237, RESULT FAIL on EXACTLY the 5a pair | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` under the lock, ANSI stripped |
| `ci-slow-c2.tail.txt` | the C2 gate's tail (the decoder + wires): EXIT=1 in 1097 s, cases=3761 pass=3523 fail=238, RESULT FAIL on the 5a pair + one oracle-side racy sample under load (`race/negative/struct-tag-alias-field`; PASS re-run alone) | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` under the lock, ANSI stripped |
| `ci-slow-tip.tail.txt` | the tip's full gate (`--slow`, the tree clean at `e453bb38`): EXIT=1 in 899 s, cases=3761 pass=3524 fail=237, RESULT FAIL on EXACTLY the 5a pair (provenance STALE for `GoLean/NativeToIR.lean`; the `google-search` line) | `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` under the lock, ANSI stripped |
| `choice-trace-main-vs-e6a.txt` | the whole-corpus choice trace, main vs the E6a tip (summary, the differing / born rows, site censuses) | `scripts/choice-trace-corpus --dump --jobs 4 --golean <bin> --out <root-relative dir>` per side (main from a `git archive main` export) + `.tmp/trace-compare.py` |

## Conclusions (the design §E6a and the handoff §1–§3 carry them in full)

1. The trigger refinement (the event-mediated form) plus `len`/`cap` over map / channel operands admits 48 + 6 sweeps and
   closes 11 of the 21 panic-vs-panic probe emitters (the 14 rows' sets reproduced, gc inside); the other 10 are grammar
   axes (interface-containing map keys, a `for` condition, generic stencils, interface comparison, a send statement, a
   slice-to-array conversion, a captured read in a lifted body).
2. The unit boundary's fall admits 39 sweeps (34 + 3 + 2; `strings`, `bytes`, `wirepb`, the twin's 7) and closes NONE of the
   151 non-main probe emitters: each is refused by the struct-type grammar (interface / defined-non-struct fields), an
   interface comparison, a library struct with an `error` field, an array base or a generic stencil — the unit boundary was
   the census's FIRST refusal reason, not the operative one. E6's exit needs those axes dispositioned (handoff §2 item 7).
3. The two decoder follow-ups refuse only forged wires (3 mutants; every positive control unchanged; the trace byte-identical
   outside E6a's rows).
4. The status-diverse set was reachable all along (`statuses=ok+panic`); the born row uses it; the E5 records are corrected.

## The full gates

The C1 `ci --diff` (frontend + twin + rows + baseline; lock 02:18:22Z–02:32:53Z): EXIT=1 in 871 s; cases=3761 pass=3524 fail=237 = the
pin 3525 / 236 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items (`certificate provenance` STALE for
`scripts/check-frontend-pins`; the `google-search` drift line); every other step ok. The C2 `ci --slow` (decoder + wires; lock
02:34:54Z–02:53:11Z): EXIT=1 in 1097 s; cases=3761 pass=3523 fail=238; RESULT FAIL on the 5a pair plus `race/negative/struct-tag-alias-field`
PASS/racy → FAIL/go-observation — the Go oracle's `-race` sample stayed green under the box's load (two whole-corpus traces ran beside the
gate); the row is outside E6a's 41 packages and PASSes re-run alone. The tip's `ci --slow` after the records commit (the tree clean at `e453bb38`; lock 02:56:19Z–03:11:18Z): EXIT=1 in 899 s; cases=3761
pass=3524 fail=237 = the pin with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items (`certificate provenance` STALE for
`GoLean/NativeToIR.lean`; the `google-search` drift line); the racy sample did not recur; every other step ok (`ci-slow-tip.tail.txt`).

## The audit fix round (2026-09-24) — `fix-round/`

[AGENT] worker. The adversarial audit `docs/2026-09-24_unseq-stage-e6a-audit.md` (candidate `1f0dee94`; FIX-FIRST, records, small);
dispositions the [AGENT] coordinator's, disclosed at the merge ask; the per-finding table is the handoff §5, the design record §E6a
«the audit fix round». Producers under the worktree's `.tmp/fix/` (replayable edit scripts and drivers; the handoff §6 names them).
Toolchain and host as above; binaries: the fix-round golean sha256 `567c0289…` (the audited tip's `bb607430…`, main's `63e9c661…`);
the frontend unchanged by the round (main's for the red-first runs from a `git archive 3fb4a0d1` tree).

| file | what | producer |
|---|---|---|
| `fix-round/diff-one-fix.txt` | `scripts/diff-one` on the SEVEN born rows (BUG-116, audit F1) on the candidate: 7 PASS/membership, enumerated=2, gc's draw exhibited | `.tmp/fix/diff-one-fix.sh` |
| `fix-round/diff-one-main-red-first.txt` | the same seven MEMBERSHIP rows on MAIN 3fb4a0d1's frontend + binary: 7 FAIL/membership — main's machine enumerates a SINGLETON (the left operand's panic); the first take's timeout noted | `.tmp/fix/diff-one-main2.sh` (main's tree `.tmp/main-tree` with the primary's `.lake` rsynced; `scripts/capped`) |
| `fix-round/diff-one-main-strict.txt` | STRICT twins of the seven subjects on main: 7 FAIL/differential — Lean the LEFT panic ≠ Go the BUILT-IN's OPERAND's panic: observed ∉ modeled, the wrong answer BUG-116 records | `.tmp/fix/diff-one-main-strict.sh` |
| `fix-round/gc-draws-fix.txt` | gc's 20 draws per born subject (5 runs × GOMAXPROCS 1/8 × default / `-N -l`): every one the built-in's operand's panic 20/20 — inside the candidate's set, outside main's singleton; tabulated + raw | `.tmp/fix/gc-draws-fix.sh` (the lane's `gc-draws.sh`) |
| `fix-round/mutants-fix.txt` | the F2 decoder change through the real CLI: the three new mutants refuse by name (main's binary decodes them); the two NATIVE positive controls run; the audit's own forged files refuse under the fix-round binary; the pinned raft twin wire decodes | by hand (the commands in the file's header) |
| `fix-round/census-fix.txt` | the census RE-TAKEN at this tree (audit F5), both frontends: 108 294 sweeps, 180 → 273 admitted (100 newly, 0 lost); probes 58 → 47 corpus, twin 128 → 128 with 3 graphs; the seven born subjects' sweeps both sides | `.tmp/fix/census-fix.sh` (the lane's census tooling) |
| `fix-round/gate-exits-fix.txt` | the standalone gates' captured exits at the fix round's tree (all green; the twin pin unchanged; `check-bugs` 116; the wire gates 55 — and their FIRST run's failure, recorded) | `.tmp/fix/gates-small.sh`, `wire-gates.sh` |
| `fix-round/ci-diff-fix-run1.tail.txt` | the SUPERSEDED first run of the full gate: its `baseline diff` step REFUSED on a malformed re-pin of the baseline (the `# reason:` block hoisted into the header — this worker's error, repaired before run 2); every other step as run 2 | `.tmp/fix/gate-ci.sh` (run 1) |
| `fix-round/ci-diff-fix.tail.txt` | the fix round's full gate: `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` under the box-wide lock (the line below) | `.tmp/fix/gate-ci.sh` |
| `fix-round/choice-trace-e6a-vs-fix.txt` | the whole-corpus choice trace, the audited tip `1f0dee94` (`.tmp/trace/e6a-rel`) vs the fix-round binary (`.tmp/trace/fix-rel`): summary, differing / born rows, site censuses (the line below) | `.tmp/fix/trace-fix.sh` + `.tmp/trace-compare.py` |

Conclusions: (1) F1 — the class is a WRONG ANSWER on main (7/7 strict twins FAIL/differential) and PASS/membership on the candidate with
gc inside; rowed, BUG-116 filed, BUG-032 corrected. (2) F2 — the scope-exact R1 environment refuses the audit's forgeries by name and
decodes every emitted wire (the two NATIVE controls, the corpus, the twin). (3) F3–F7 — records corrected as the handoff §5 table says.

The full gate of the fix round: `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the fix round's tree (runtime commit `973119c2` + the
records, all in the working tree; the box-wide lock 2026-09-24T04:46:13Z–04:58:35Z): EXIT=1 in 742 s; cases=3768 pass=3531 fail=237 = the pin
3768 = 3532 / 236 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items (`certificate provenance` STALE for
`GoLean/NativeToIR.lean`; the `google-search` drift line); every other step ok (`fix-round/ci-diff-fix.tail.txt`; a first run's `baseline diff` REFUSED on a malformed re-pin of the baseline — this worker's
error, repaired before run 2 — `fix-round/ci-diff-fix-run1.tail.txt`). The whole-corpus choice
trace vs the audited tip `1f0dee94`: 3732 ids, 3725 byte-identical, 0 DIFFER, 0 ONLY_A, 7 ONLY_B (the born rows); `unseqNext` 2550 → 2595,
every other site identical; 34 / 34 export refusals (`fix-round/choice-trace-e6a-vs-fix.txt`).
