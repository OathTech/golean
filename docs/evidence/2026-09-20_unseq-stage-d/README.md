# Stage D — the workload ladder (routes β and α), the corpus scan, gate tails (2026-09-20)

[AGENT] Evidence for lane `core/unseq-stage-d-0920` (worktree `.claude/worktrees/unseq-stage-d`; base main
`f14a05e5`, rebased onto `10d2f2dc`). Consuming docs: `docs/2026-09-20_unseq-stage-d-design.md`,
`docs/2026-09-20_unseq-stage-d-handoff.md`. Small records only (caps 256 KiB / 4 MiB); every number is copied from the
named log under the lane worktree's `.tmp/` (untracked); the scratch drivers are appended as `*.txt` — they are GLUE
over the existing drivers (`CLI.enumSetup` → `CLI.explore` for β; `CLI.runDedupObservations` → `EnumDedup.buildCert` +
the VERIFIED `checkCert` for α; `golean coverage-observations` for the corpus), never a driver of their own.

- Toolchain: Lean `leanprover/lean4:v4.32.2` (repo pin); `go version go1.26.5 linux/amd64` (= the oracle pin) for the
  wires. Host: linux/amd64, 32 cores, 125 GiB, shared box (the r44 train ran until its close; a rebuild of this tree
  invalidated one β run — see §2). Every lake/lean command through `scripts/capped` (32 GiB during the held lock).
- Binaries: main `10d2f2dc`'s `golean` sha256 `90024323dbe000827fe6abc4abfe39c8dd084df5b3debddf574a9aee0a2874a4`
  (= this tree before D1: identical Lean sources); the D1 tree's `golean` sha256
  `a5c1aca0d27aa6f3c6377b1c25eadc7989a18fe76eb12da00a76af7ea20090c4` (the ladder, the corpus scan and the set
  comparison ran on it); the runtime commit's binary `0681abc69cf90894e483b4ee896f0b6b5fc0592f70a4612d5a222f85d1fce64a`
  differs from it by ONE docstring (`consumesUnseqPanic`, Machine.lean) — the gate and the whole-corpus trace ran on
  this one. Route β's numbers are invariant under D1 (the
  DFS explorer does not read `innerVecs`): the pre-D1 partial run (`ladder-beta-pre-d1-partial.tsv`, 32 rungs) and the
  D1 run agree rung for rung on members/leaves/sites/steps (wall indicative).

## 1. Files

| file | what | producer |
|---|---|---|
| `Ladder.lean.txt`, `ladder-run.sh.txt` | the rung programs (`loop N`, `wide k`, `nest M`; silent/printing) and the per-rung runner (`/usr/bin/time -v` around `lake env lean --run`) | this lane |
| `ladder-beta.tsv` | route β, every rung: members, leaves (= paths), sites, steps, probes, maxDepth, in-process wall, `time -v` wall, max RSS | `ladder-run.sh beta` on the D1 binary |
| `ladder-alpha.tsv` | route α, every rung: the dedup driver's stats line (observations, nodes = unique states, edges, dedupHits) or its refusal by name; wall, RSS | `ladder-run.sh alpha` |
| `ladder-heap.tsv` | the canonical tape through `execProgLoop`: final heap size / `nextAddr` per `loop N` — the per-sweep cell cost (D2, for C4) | `ladder-run.sh heap` |
| `ladder-beta-pre-d1-partial.tsv` | the first β run (pre-D1 binary), rungs 1–32; the rest of that run died on a concurrent rebuild («object file … does not exist») — superseded, kept as the β-invariance cross-check | — |
| `alpha-scan.sh.txt`, `alpha-corpus-rows.tsv` | the route-α CORPUS scan: 153 rows of the ladder's packages through `golean coverage-observations --engine dedup` (the row's `width`/`sites`, work 20 M, cap 4096): CLOSED (observations, nodes, hits) or the refusal class | this lane, D1 binary |
| `alpha-vs-beta.sh.txt`, `alpha-vs-beta-sets.tsv` | for every CLOSED row, BOTH engines' printed member sets compared exactly (sorted JSON lines): 100/100 SAME | this lane, D1 binary |
| `twin-control-trace.txt` | `scripts/choice-trace-corpus --dump` over the five `multipkg/mini-raft-twin` rows: 569 consumptions, all `appendSpill`, 0 `unseqNext`/`unseqPanic`, observation invariant over the six streams | the tracer, D1 binary |
| `gate-tail.txt` | `scripts/capped scripts/ci --slow` at the runtime commit: the differential summary, the DRIFT lines and the step summary (ANSI stripped) | this lane |

## 2. Route β (the default DFS explorer; fuel 2 000 000, width 8, sites 64, cap 4096, work 50 000 000)

Silent `loop N` (members 1; paths 2^N):

| N | members | leaves (paths) | sites | steps | probes | maxDepth | explore wall ms | `time -v` wall | max RSS kB |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 1 | 2 | 1 | 181 | 3 | 1 | 5 | 0:00.36 | 766052 |
| 2 | 1 | 4 | 3 | 467 | 9 | 2 | 15 | 0:00.37 | 766976 |
| 3 | 1 | 8 | 7 | 1039 | 21 | 3 | 42 | 0:00.41 | 770076 |
| 4 | 1 | 16 | 15 | 2183 | 45 | 4 | 101 | 0:00.47 | 768368 |
| 5 | 1 | 32 | 31 | 4471 | 93 | 5 | 239 | 0:00.60 | 768756 |
| 6 | 1 | 64 | 63 | 9047 | 189 | 6 | 563 | 0:00.94 | 771472 |
| 7 | 1 | 128 | 127 | 18199 | 381 | 7 | 1267 | 0:01.64 | 771728 |
| 8 | 1 | 256 | 255 | 36503 | 765 | 8 | 2847 | 0:03.23 | 770268 |
| 9 | 1 | 512 | 511 | 73111 | 1533 | 9 | 6377 | 0:06.75 | 772436 |
| 10 | 1 | 1024 | 1023 | 146327 | 3069 | 10 | 13837 | 0:14.20 | 770392 |
| 11 | 1 | 2048 | 2047 | 292759 | 6141 | 11 | 29751 | 0:30.11 | 770184 |
| 12 | 1 | 4096 | 4095 | 585623 | 12285 | 12 | 65936 | 1:06.30 | 771332 |

Printing `loop N`:

| N | members | leaves (paths) | sites | steps | probes | maxDepth | explore wall ms | `time -v` wall | max RSS kB |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 2 | 2 | 1 | 205 | 3 | 1 | 6 | 0:00.40 | 766844 |
| 2 | 4 | 4 | 3 | 539 | 9 | 2 | 18 | 0:00.42 | 766732 |
| 3 | 8 | 8 | 7 | 1207 | 21 | 3 | 46 | 0:00.41 | 769412 |
| 4 | 16 | 16 | 15 | 2543 | 45 | 4 | 112 | 0:00.50 | 767256 |
| 5 | 32 | 32 | 31 | 5215 | 93 | 5 | 274 | 0:00.63 | 768084 |
| 6 | 64 | 64 | 63 | 10559 | 189 | 6 | 636 | 0:01.03 | 767984 |
| 7 | 128 | 128 | 127 | 21247 | 381 | 7 | 1512 | 0:01.91 | 769920 |
| 8 | 256 | 256 | 255 | 42623 | 765 | 8 | 3303 | 0:03.69 | 771064 |
| 9 | 512 | 512 | 511 | 85375 | 1533 | 9 | 7490 | 0:07.87 | 771480 |
| 10 | 1024 | 1024 | 1023 | 170879 | 3069 | 10 | 16806 | 0:17.21 | 773976 |
| 11 | 2048 | 2048 | 2047 | 341887 | 6141 | 11 | 38118 | 0:38.49 | 773768 |
| 12 | 4096 | 4096 | 4095 | 683903 | 12285 | 12 | 88170 | 1:28.55 | 781728 |
| 13 | REFUSED by name: «observation cap N=4096 exceeded — the case is too wide for enumeration (design note: needs» | | | | | | 90405 | 1:30.78 | 780464 |

Printing `loop N` (members = paths): N = 1..12 close; **N = 13: REFUSED by name — «observation cap N=4096 exceeded — the
case is too wide for enumeration»** (90–96 s spent before the refusal in the two runs; the cap is a REFUSAL, never a
truncation — N3).

`wide k` silent (paths k!): k = 8 → 40 320 leaves, 28 961 sites, 4 145 044 steps, 254–256 s in the two runs (`time -v`
4:14.62 / 4:16.77) — the last rung under 50 M work. Printing: k = 7 REFUSED (5 040 > 4 096). `wide k` silent:

| N | members | leaves (paths) | sites | steps | probes | maxDepth | explore wall ms | `time -v` wall | max RSS kB |
|---|---|---|---|---|---|---|---|---|---|
| 2 | 1 | 2 | 1 | 180 | 3 | 1 | 6 | 0:00.36 | 766100 |
| 3 | 1 | 6 | 4 | 567 | 12 | 2 | 19 | 0:00.39 | 766108 |
| 4 | 1 | 24 | 17 | 2296 | 51 | 3 | 82 | 0:00.47 | 764784 |
| 5 | 1 | 120 | 86 | 11647 | 258 | 4 | 474 | 0:00.84 | 768084 |
| 6 | 1 | 720 | 517 | 71178 | 1551 | 5 | 3349 | 0:03.72 | 767408 |
| 7 | 1 | 5040 | 3620 | 508093 | 10860 | 6 | 27432 | 0:27.81 | 769608 |
| 8 | 1 | 40320 | 28961 | 4145044 | 86883 | 7 | 256378 | 4:16.77 | 766624 |

`wide k` printing:

| N | members | leaves (paths) | sites | steps | probes | maxDepth | explore wall ms | `time -v` wall | max RSS kB |
|---|---|---|---|---|---|---|---|---|---|
| 2 | 2 | 2 | 1 | 204 | 3 | 1 | 7 | 0:00.37 | 765380 |
| 3 | 6 | 6 | 4 | 657 | 12 | 2 | 20 | 0:00.38 | 768552 |
| 4 | 24 | 24 | 17 | 2680 | 51 | 3 | 90 | 0:00.48 | 768176 |
| 5 | 120 | 120 | 86 | 13597 | 258 | 4 | 531 | 0:00.89 | 769716 |
| 6 | 720 | 720 | 517 | 82914 | 1551 | 5 | 3999 | 0:04.39 | 767704 |
| 7 | REFUSED by name: «observation cap N=4096 exceeded — the case is too wide for enumeration (design note: needs» | | | | | | 31545 | 0:31.91 | 774048 |

`nest M` silent (paths 6^M):

| N | members | leaves (paths) | sites | steps | probes | maxDepth | explore wall ms | `time -v` wall | max RSS kB |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 1 | 6 | 4 | 717 | 12 | 2 | 21 | 0:00.39 | 764764 |
| 2 | 1 | 36 | 28 | 4683 | 84 | 4 | 207 | 0:00.59 | 765712 |
| 3 | 1 | 216 | 172 | 28479 | 516 | 6 | 1625 | 0:02.02 | 766484 |
| 4 | 1 | 1296 | 1036 | 171255 | 3108 | 8 | 12113 | 0:12.49 | 771052 |
| 5 | 1 | 7776 | 6220 | 1027911 | 18660 | 10 | 87440 | 1:27.85 | 772268 |

`nest M` printing:

| N | members | leaves (paths) | sites | steps | probes | maxDepth | explore wall ms | `time -v` wall | max RSS kB |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 6 | 6 | 4 | 807 | 12 | 2 | 24 | 0:00.42 | 767652 |
| 2 | 36 | 36 | 28 | 5313 | 84 | 4 | 224 | 0:00.63 | 769032 |
| 3 | 216 | 216 | 172 | 32349 | 516 | 6 | 1899 | 0:02.29 | 769000 |
| 4 | 1296 | 1296 | 1036 | 194565 | 3108 | 8 | 14722 | 0:15.11 | 771424 |
| 5 | REFUSED by name: «observation cap N=4096 exceeded — the case is too wide for enumeration (design note: needs» | | | | | | 58311 | 0:58.69 | 771780 |

Reading: steps ≈ paths × (steps per path) — the DFS shares prefixes, not states; wall 16–23 ms/path at `loop 12`
(66 s and 94 s in the two runs; probes included: 3 alias-ladder replays per site); RSS flat at ~760–780 MB (the loaded
oleans; the DFS is in the noise).

## 3. Route α (the certified dedup engine; the same caps, work 50 000 000)

`loop N` (unique states = 154 + 115·(N−1): LINEAR where β's paths are 2^N):

| N | observations | unique states (nodes) | edges | dedupHits | `time -v` wall | max RSS kB | printing variant |
|---|---|---|---|---|---|---|---|
| 1 | 1 | 154 | 154 | 1 | 0:00.39 | 761960 | refused by name (output event) |
| 2 | 1 | 269 | 270 | 2 | 0:00.38 | 763660 | refused by name (output event) |
| 3 | 1 | 384 | 386 | 3 | 0:00.38 | 763472 | refused by name (output event) |
| 4 | 1 | 499 | 502 | 4 | 0:00.42 | 763396 | refused by name (output event) |
| 5 | 1 | 614 | 618 | 5 | 0:00.42 | 760864 | refused by name (output event) |
| 6 | 1 | 729 | 734 | 6 | 0:00.43 | 765248 | refused by name (output event) |
| 7 | 1 | 844 | 850 | 7 | 0:00.44 | 763492 | refused by name (output event) |
| 8 | 1 | 959 | 966 | 8 | 0:00.43 | 765064 | refused by name (output event) |
| 9 | 1 | 1074 | 1082 | 9 | 0:00.44 | 763104 | refused by name (output event) |
| 10 | 1 | 1189 | 1198 | 10 | 0:00.48 | 761232 | refused by name (output event) |
| 11 | 1 | 1304 | 1314 | 11 | 0:00.46 | 763260 | refused by name (output event) |
| 12 | 1 | 1419 | 1430 | 12 | 0:00.49 | 760864 | refused by name (output event) |

`wide k` (the state graph of k unordered invocations is exponential in k — the done-set lattice — but far below k!):

| N | observations | unique states (nodes) | edges | dedupHits | `time -v` wall | max RSS kB | printing variant |
|---|---|---|---|---|---|---|---|
| 2 | 1 | 149 | 149 | 1 | 0:00.40 | 765308 | refused by name (output event) |
| 3 | 1 | 332 | 336 | 5 | 0:00.40 | 763744 | refused by name (output event) |
| 4 | 1 | 771 | 787 | 17 | 0:00.48 | 765212 | refused by name (output event) |
| 5 | 1 | 1806 | 1854 | 49 | 0:00.74 | 760728 | refused by name (output event) |
| 6 | 1 | 4201 | 4329 | 129 | 0:02.03 | 762736 | refused by name (output event) |
| 7 | 1 | 9652 | 9972 | 321 | 0:08.04 | 767328 | refused by name (output event) |
| 8 | 1 | 21887 | 22655 | 769 | 0:37.42 | 773308 | — |

`nest M` (linear: 372 + 315·(M−1)):

| N | observations | unique states (nodes) | edges | dedupHits | `time -v` wall | max RSS kB | printing variant |
|---|---|---|---|---|---|---|---|
| 1 | 1 | 372 | 376 | 5 | 0:00.41 | 765888 | refused by name (output event) |
| 2 | 1 | 687 | 696 | 10 | 0:00.45 | 765016 | refused by name (output event) |
| 3 | 1 | 1002 | 1016 | 15 | 0:00.46 | 763120 | refused by name (output event) |
| 4 | 1 | 1317 | 1336 | 20 | 0:00.49 | 763564 | refused by name (output event) |
| 5 | 1 | 1632 | 1656 | 25 | 0:00.55 | 763072 | refused by name (output event) |

Every printing variant: «output event at node … (a print/println step wrote 1 chunk(s)): engine=dedup keys nodes on state and output is a trace — this row cannot use engine=dedup (use the default enumerator)» — a refusal by name, the engine's standing G-OUT rule (design note §5).

## 4. The corpus rungs (D1 binary)

`alpha-corpus-rows.tsv`: 153 rows — **100 CLOSED** (certified; 41 membership rows each with its declared `members=`
count reproduced, 59 strict rows each a singleton), **42 REFUSE:output** (a `print`/`println` step — the engine keys
nodes on state and output is a trace), **8 REFUSE:row-refusal** (the machine's own refusal at node 0 —
BUG-102/BUG-104's designed reds, `frontend-quarantined`), **3 REFUSE:pre-existing shapes** (`mapIterK` ×1,
`appendSpill` ×2). `alpha-vs-beta-sets.tsv`: the 100 certified sets EQUAL the DFS's sets, row by row.
`spec-examples-stmt/continue-label`: α `observations=1 nodes=5122 edges=5145 dedupHits=24 certified=checkCert`
(77 ms); β `observations=1 steps=39646083 probes=85290 sites=28430 leaves=32805 maxdepth=18` — the same singleton.

## 5. D2 — the accountant and the per-sweep cell cost

Every β enumeration above ran under the explorer's two-sided sentinel (0 drift alarms; an alarm fails the enumeration
by name); the twin trace's validator: 569 consumptions checked, 0 menu-invariant violations, 0 mirror/accountant/
sentinel/pick-record alarms, 0 driver-agreement mismatches. `ladder-heap.tsv`: `loop N` ends with heap = 3 + 4N cells
(`ladder-heap.tsv`):

| N | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| final heap cells (= 3 + 4N) | 7 | 11 | 15 | 19 | 23 | 27 | 31 | 35 | 39 | 43 | 47 | 51 |
 — 2 binder cells + 2 callee result cells per sweep, none reclaimed (C4's lane).

## 6. Gate

Gate: `scripts/capped scripts/ci --slow` at the runtime commit (this tree; the box-wide lock held 21:50–22:06Z),
EXIT=1 in 946 s — RESULT FAIL on EXACTLY the expected red: `certificate provenance` (STALE certification: changed
dependency `build/files/GoLean/CLI.lean`; the fresh re-certification reports the UNCHANGED six-member `google-search`
set, 187 s — the train installs the candidate at step 5a, not a re-pin here) and `baseline diff` DRIFT = exactly
`imported-goose/channel/google-search` PASS/membership → FAIL/membership (the same 5a-class item) + `spec-examples-stmt/
continue-label` PASS/- → PASS/confluent (the named lane move; re-pinned in the runtime commit with the written reason).
Every other step ok: core build warning-free; escape-hatch preflight/addendum/meta-layer; core totality audit (every
GoLean/ module, required core theorems, poison controls); engine-isolation; check-mem-callsites; admission proofs;
declaration + wire boundaries; method identity; unseq scheduler (Stage B; 35 theorems); unseq wire (Stage C); frontend
pins (twin wire = pinned bytes); frontend/lowerdiag/harness unit tests; eval tests 274 ok; differential 3705 rows
3458 PASS / 247 FAIL (= the pin with the one 5a-class row red); lane-validation fixtures incl. the go half; negative
corpus 394 matched; FloatVectors + inittask-std byte-exact; executed library coverage PASS. `beside-loop` (the
baseline's alternation row) did not drift. Gate tail: `docs/evidence/2026-09-20_unseq-stage-d/gate-tail.txt`.
