# The hygiene slice — execution log (2026-08-28)

The scheduled debt batch of the corpus-first Iris era: unit **H** of
`docs/2026-08-28_iris-corpus-plan.md` §6.3, four items, all
[USER]-ruled or audit-flagged. Lane `w1-prover`, branch
`hygiene-slice`, forked from `main` @ `05e81b70`. One writer; the
sibling `u0-iris` worker's file set (lakefile/manifest/deps + its
survey doc) is disjoint from this one by design and was not touched.

*Quantifier-audit line ([AGENT]): this unit advances NO quantifier and
says so — it is debt retirement plus one gate-apparatus hardening. Per
charter, that must be stated, not implied.*

**Provenance key**: [USER] = a user decision on the record; [AGENT] =
an executor judgment inside the written boundaries of this slice.

---

## 1. Item 1 — the `ChoiceCanon` kill

**Authority**: [USER] ruling 2026-08-28, rationale on the record —
choice-invariance rolls up into the reasoning layer: with a points-to,
the choices outside the footprint are frame-irrelevant, so G-REPR's
footprint subsumption replaces the erasure instrument (plan §4.2,
§6.3).

**The K-3 consumer check, run BEFORE deleting anything** (the STOP
discipline: if anything live consumed the module beyond the root
aggregator and the pin file, stop and report). Searched the whole tree
for the module path, for the namespace `GoLean.Frame.ChoiceErase`, and
for every public name in it (`CForm`, `canonStateM`, `canonState`,
`CEquivM`, `CEquiv`, `CleanForm(M)`, `Mask`, `collectFix`, `emitCell`,
`serMany`, `isZeroLike`, …), across `*.lean`, `*.md`, `*.json`,
`*.toml`, `*.sh`, plus `scripts/` and both lakefiles. Result:

| reference | kind | disposition |
|---|---|---|
| `proofs/GoLeanProofs.lean:72` | root aggregator import | removed |
| `proofs/Audit/ChoiceInv.lean:1` + 4 pins | the pin file | file deleted |
| docs (registry, ARCHIVE, triage/kill-list, campaign logs) | prose | history; the live ones corrected |

**Zero live proof consumers. No STOP condition met.** [AGENT]

**What was deleted**:

- `proofs/GoLeanProofs/Frame/ChoiceCanon.lean` — 616 lines, the whole
  `~`/`~ₘ` carrier.
- `proofs/Audit/ChoiceInv.lean` — 45 lines. **Checked what else it
  pinned before deciding, as instructed**: after the triage pruned its
  `ChoiceInv` pins (K-3, 2026-08-27) the file contained the four
  `ChoiceCanon` carrier pins and nothing else but tombstone prose.
  Nothing survives the carrier's death → **the file goes too**, and
  its import at `proofs/Audit.lean:32` with it. [AGENT] (the
  brief's "if nothing survives in it" branch, taken on the evidence)

**Records**: `docs/ARCHIVE.md` gains a hygiene-slice section — no new
archive ref for a one-file kill; the recovery citation is the pre-kill
commit **`05e81b70`**. It carries the plan-mandated park-record note:
the parked SpanIso lane consumed `Mask`, and at its resume it
re-derives or harvests from `05e81b70` — it may not import the dead
module back. The mechanism registry's `ChoiceCanon` row and triage
addendum are marked KILLED, and the stale "survived the reset" line in
`ARCHIVE.md` is corrected.

**Commit** `1ab8bbc7` — 6 files, +60 / −675.

---

## 2. Item 2 — the `Audit.lean` provenance comment [TRUST-ADJACENT]

**Authority**: deferred pre-merge gate-audit finding **M-1**.

The designated-list comment recorded the fork/join reclassification as
a flat "USER decision at the triage-plan sign-off". Corrected to the
accurate two-act provenance, in the wording already used for the
parallel M-1 fix in `docs/ARCHIVE.md`:

> AGENT coordinator recommendation ratified by USER package assent
> (2026-08-27); the reclassification act itself USER-confirmed at the
> merge (2026-08-28).

**The parser constraint, respected.** This comment sits INSIDE the
region `scripts/comparator-judge` extracts the designated list from.
The provenance tags are therefore written WITHOUT their usual square
brackets, and the comment contains no square bracket of any kind —
verified by `grep '[][]'` over the edited region (no hits). The
comment now states this reason itself, so the next editor does not
re-introduce the hazard.

**Verification** — the wrapper's own extraction command
(`scripts/comparator-judge:129`) run against the edited file:

| | names extracted |
|---|---|
| before the edit | **51** |
| after the edit | **51** |
| short-name set vs `judge-config.json` | identical (diff empty) — lockstep intact |

**DELTA FLAG**: trust-adjacent. `proofs/Audit.lean` is the
statement-TCB gate. The designated SET is unchanged (comment text
only), but Audit.lean MOVED, which **triggers the comparator-judge
landmark at this slice's ceremony** (§5 below).

**Commit** `4d29aab4` — 1 file, +15 / −4.

---

## 3. Item 3 — judge-parser hardening [TRUST-ADJACENT]

**Authority**: gate-audit follow-up **L-3**. `scripts/comparator-judge`
is OUR apparatus, not an external trust tool — the charter permits it
to evolve under the gates with the edit delta-flagged. The external
tools (comparator, lean4export, landrun) were **not** touched; their
pins are unchanged and were verified pristine before the run.

**The hazard.** The extraction used the sed range

```
/let designated : List Name := \[/,/\]/
```

whose end pattern is "the first line containing a `]` ANYWHERE". The
list carries interleaved provenance comments, so a `[USER]` tag in one
of them ends the range early and the designated list is silently
TRUNCATED — the lockstep compare then runs against a short list. Fixed
comment-side at the 2026-08-27 triage; fixed parser-side here.

**The change** — one range expression plus its explanatory comment
(which cites the 2026-08-27 hazard). The end is anchored to the list's
ACTUAL closing line — an optional name literal followed by the closing
bracket (`  ``Ns.thm]`, today's shape), or a bare `]` should the list
ever be reflowed:

```
sed -n -E '/let designated : List Name := \[/,/^[[:space:]]*(``[A-Za-z0-9_.]+)?\][[:space:]]*$/p'
```

A comment line can no longer terminate the range: it would have to
consist of nothing but a name literal and a bracket. **Fail-closed in
the other direction too** — if the terminator is never matched the
range runs to EOF, the surplus names break the lockstep diff, and the
run FAILS. It can never yield a silently short list. The emptiness
guard and the lockstep diff are untouched.

**Verification by extraction, four ways** (test done locally, by
extraction only; the bracket-injected copy was written under
gitignored `artifacts/` and deleted — **no test pollution committed**,
`git status` clean before the commit):

| input | OLD parser | NEW parser |
|---|---|---|
| clean `Audit.lean` | 51 | **51** |
| `Audit.lean` + a deliberate `-- … [USER] … ]` comment injected inside the list | **33** ← the hazard, reproduced | **51** ← hazard defeated |

The 51→33 truncation is the 2026-08-27 failure reproduced exactly.

**DELTA FLAG**: trust-adjacent — the judge wrapper. Behaviour on
well-formed input is unchanged (51 = 51); the change strictly narrows
what can terminate the range.

**Commit** `17d23216` — 1 file, +14 / −1.

---

## 4. Item 4 — `fjRunDeadlocks` retirement

**Authority**: gate-audit **L-7**, plan §6.3 ("retire the def +
theorems + pins").

**Consumer check first.** `fjRunDeadlocks` was referenced by exactly
two declarations in the tree: `forkJoinDeadlockCanonical` and
`forkJoinDeadlockAdversarial` (`Specs/GoldenForkJoin.lean:82,86`) —
the two pinned-stream kernel replays de-designated at the triage
landing and named for retirement in the SAME plan item, i.e. not
survivors. Zero references from `Challenge.lean`, `Solution.lean`,
`judge-config.json`, or any other module. Separately confirmed, as the
brief asked: `fjRunGives42` and `fjReadout42` ARE legitimately used —
by the designated ∀-schedule family — and **stay**. **No STOP
condition met.** [AGENT]

**What was deleted**:

- `Specs/ForkJoinTargets.lean`: `fjRunDeadlocks`, and with it the
  deadlock program cluster it was the only consumer of —
  `fjBlockedWorker`, `fjDeadlockDriver`, `fjDeadlockSeed`.
  **THE FILE STAYS** (it is a target of ci's surface-purity import
  scan, `scripts/ci:463`); only defs go. [AGENT], per the brief's NB.
- `Specs/GoldenForkJoin.lean`: the two theorems → a retirement note.
- `proofs/Audit.lean`: their two `#print axioms` pins.

**Why nothing is lost**: `forkJoinNoDeadlock` says ∀ ch, the fork/join
program never reaches the `.deadlock` terminal — ∀-quantified, where
the retired pair replayed two pinned streams of a *different*
(deliberately deadlocking) program. The pair's non-vacuity role for
`forkJoinAllStreamsCert` survives as a recorded probe note in that
theorem's docstring rather than as a live kernel replay.

Prose corrected wherever it cited the retired names: both module
docstrings, the `forkJoinAllStreamsCert` docstring, `Challenge.lean`'s
reclassification note, and the designated-list comment in `Audit.lean`
(kept bracket-free per that region's convention). Parser re-verified
after those Audit.lean edits: 51 names, lockstep intact.

**Commit** `1022a6c2` — 4 files, +62 / −67.

---

## 5. Ceremony

### 5a. `scripts/ci` — PASS

Box-wide build lock taken before the run
(`mkdir /home/dev/projects/golean/artifacts/build-lock.d`, owner file
written, released after the ceremony) per
`docs/operational-lessons.md`. Run:

```
GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=48G scripts/capped scripts/ci
```

**`EXIT=0`, RESULT: PASS** (`artifacts/hygiene/ci.log`). Cap 48G →
`LEAN_NUM_THREADS=6`. Builds: 58 / 521 / 61 jobs.

`GOLEAN_ALLOW_NO_DIFF=1` note, stated visibly as required: this
worktree has no recorded differential/negative run, and the gate said
so in the clear — `negative baseline diff NOT RUN (no record;
explicitly allowed here)` and `differential baseline diff NOT RUN (no
record; explicitly allowed here)`. The hatch is **in scope**: this
slice touches **no runtime code** — no `GoLean/GoCore/`, no frontend,
no interpreter. Deletions and comments only.

**What the gate said about the `scripts/` edit (item 3), as asked**:
ci has no self-hash or purity step over `scripts/`, so the wrapper
edit passed through it unremarked. ci's only word on the judge is its
staleness/scope note, which fired as expected and is report-only:

```
note comparator landmark: last certified run 51 theorems in 122s @ c2e1824d7eb9 (2026-08-27), 8 commit(s) ago
note comparator landmark OWED (scope): 4 file(s) in Challenge's trusted closure changed since that run — run scripts/comparator-judge (report-only, never blocks)
```

That obligation is discharged by 5b.

### 5b. `scripts/comparator-judge` — landmark (TRIGGERED)

Triggered because `proofs/Audit.lean` moved (item 2), and independently
owed by ci's scope note. Trust-tool pins verified **before** the run,
all pristine (the wrapper fail-closes on each anyway):

| tool | rev / path | state |
|---|---|---|
| `deps/comparator` | `fd2e25de155523dbce1f35d410511f9f63998461` (= pin) | tree pristine, binary built |
| `lean4export` | `8554815c2dc6b7abe99ec1f08849c9759ba77947` (= pin) | tree pristine, binary built |
| `landrun` | `~/go/bin/landrun` | present at its pinned modver |

Run bare (not under `scripts/capped` — the wrapper manages its own
confined build; this matches the 2026-08-27 landmark's invocation),
with the box lock still held.

**`EXIT=0` — PASS: 51 theorems certified in 117 s, fresh clone @
`1022a6c221a5`** (`artifacts/hygiene/judge.log`). The confined unit
reported `Lean default kernel accepts the solution` /
`Finished with result: success`, `status=0`, runtime 1 min 56.7 s,
memory swap peak 0B. The wrapper appended its marker

```
LANDMARK-RUN: 1022a6c221a5 2026-08-28 51 117
```

to `docs/2026-08-02_comparator-judge-sprint.md`, committed with this
log.

**Like-for-like**: 51 theorems, exactly as at the previous landmark
(`c2e1824d7eb9`, 2026-08-27, 51 in 122 s). The designated set did not
move in this slice — items 2 and 3 were comment/parser work, and item
4 retired only ALREADY-de-designated theorems. 51 = 51 is the
cross-check that the parser hardening changed no behaviour on the real
list, run end-to-end through the judge rather than by extraction
alone. (The older 56-theorem anchors predate the triage's five-row
reclassification and are not comparable.)

---

## 6. Deltas and delta-flags for the landing review

`git diff --stat 05e81b70..HEAD`: **10 files, +151 / −747** (net −596
lines; 661 lines of Lean deleted, of which 616 are `ChoiceCanon`).

| commit | item | files | +/− | flag |
|---|---|---|---|---|
| `1ab8bbc7` | 1 — ChoiceCanon kill | 6 | +60 / −675 | — |
| `4d29aab4` | 2 — Audit.lean provenance | 1 | +15 / −4 | **TRUST-ADJACENT** (statement-TCB gate file; comment only, designated set unchanged) |
| `17d23216` | 3 — judge parser | 1 | +14 / −1 | **TRUST-ADJACENT** (judge wrapper; behaviour unchanged on well-formed input) |
| `1022a6c2` | 4 — fjRunDeadlocks | 4 | +62 / −67 | — (touches `Challenge.lean` prose only) |

**For the reviewer's attention**, honestly stated:

1. Two trust-adjacent commits (2, 3). Neither changes the designated
   set, the axiom allowlist, the interpreter, or any statement's
   meaning; both are verified by extraction counts recorded above.
2. `proofs/Challenge.lean` — the judge's trusted root — is touched in
   item 4, **comment text only**; its theorem statements are
   untouched, as the judge run independently certifies.
3. `Audit/ChoiceInv.lean` was deleted whole. That is a **pin count
   reduction of 4** (carrier pins) **+ 2** (the fork/join deadlock
   pins in item 4) = 6 fewer `#print axioms` pins in the build. Every
   one of them pinned a declaration that no longer exists.
4. The `GOLEAN_ALLOW_NO_DIFF=1` hatch was used; scope argument in 5a.
5. Nothing in this slice is a merge or a push. Branch-complete is the
   end state; both remain the user's calls.
