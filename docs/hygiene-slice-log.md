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

> **⚠ THIS ITEM WAS WRONG AND IS SUPERSEDED — see §7, fix F-1.** The
> rewrite below applied M-1's wording to a row M-1 explicitly
> excluded, re-attributing a reserved [USER] act to an [AGENT]
> recommendation. It is left standing here as the record of what was
> done and caught; the corrected text is in §7. Do not read the
> wording in this section as the record.

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
consist of nothing but a name literal and a bracket.

**The failure direction, stated exactly** (corrected per audit finding
F-3 — the first version of this section overstated it): the guarantee
this change buys is **"never a silent SHORT list"**. If the terminator
is never matched the range runs to EOF, and on today's file that
yields **exactly 51 names**, not more — re-measured at this tip: zero
`` `` name literals appear after the list's closing line. So the
surplus-breaks-the-lockstep-diff mechanism does not engage today; it
only engages if name literals ever come to follow the list. The
emptiness guard and the lockstep diff are untouched.

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

**What is kept, and what is genuinely LOST** (this section was headed
"Why nothing is lost" and overstated; corrected per audit finding
F-5):

- *Kept*: the deadlock-FREEDOM content. `forkJoinNoDeadlock` says ∀
  ch, the fork/join program never reaches the `.deadlock` terminal —
  ∀-quantified, where the retired pair replayed two pinned streams of
  a *different* (deliberately deadlocking) program.
- *Lost*: the retired pair was also the only **discriminating**
  witness for `allStreamsOkPool`. Its deadlock program was probed
  against that checker and REFUSED; with the pair gone there is **no
  surviving in-tree demonstration that the checker can return
  `false`** — verified at this tip, every in-tree use of
  `allStreamsOkPool` is a `= true` certificate. The checker's
  discrimination is **UNWITNESSED in-tree**; the probe survives only
  as an archived record (`docs/ARCHIVE.md`, recoverable at
  `05e81b70`). This is a real evidentiary gap: a checker that
  returned `true` unconditionally would satisfy every live use. The
  named re-supplier is the corpus's fork/join member when concurrency
  resumes (plan §5), whose negative twin restores a live
  false-witness. `Specs/GoldenForkJoin.lean`'s docstring and the
  ARCHIVE entry now say exactly this.

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

**Measured at `1022a6c2`, the pre-audit tip** (relabelled per audit
finding F-4 — this figure was originally presented as HEAD, which it
had ceased to be once the log commit landed). The fix round's own
deltas and the cumulative figure at the final tip are in §7.

`git diff --stat 05e81b70..1022a6c2`: **10 files, +151 / −747** (net
−596 lines; 661 lines of Lean deleted, of which 616 are
`ChoiceCanon`).

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

---

## 7. Fix round — the pre-merge audit's FIX-FIRST verdict (2026-08-28)

The pre-merge adversarial audit of this slice returned **FIX-FIRST**
with one HIGH finding. The auditor's mechanical verdicts on the kills,
the consumer sweeps and the parser were CLEAN — it reproduced the
verification independently and probed the regex adversarially. **The
defects were record-level, and F-1 is a real provenance error of
mine.** [AGENT]

### F-1 (HIGH) — the designation act's provenance, restored

**The error.** Item 2 copied the M-1 house wording — "AGENT
coordinator recommendation ratified by USER package assent" — onto the
fork/join reclassification row. **M-1's scope never covered that
row.** `docs/triage-execution-log.md:29-32` records triage decision 3
as "**[USER] decision** (the designation act is the user's alone;
correctly recorded as such at birth and unchanged here)", and the fix
table at :229 says in terms: "Decision 3 unchanged — the designation
act was the user's." M-1 re-attributes decisions **1, 2, 4, 5** only.

So the edit **re-attributed a reserved [USER] act to an [AGENT]
recommendation, inside the statement-TCB gate file** — precisely the
class the charter names a critical trust failure. The lesson [AGENT]:
I pattern-matched a house wording onto a neighbouring row instead of
reading the finding's scope. Provenance is per-decision; it is never
inferred from a sibling.

**The corrected record** (`proofs/Audit.lean`, bracket-free convention
and parser-hazard NB both kept), asserting nothing without citation:

- the reclassification was a **USER decision at the triage sign-off**
  — the designation act is the USER's alone, correctly recorded as
  such at birth;
- it was **USER-reconfirmed at the 2026-08-28 triage-landing merge**,
  and the comment **cites where that record lives** rather than
  restating it: `docs/raft-campaign-log.md`, entry 2026-08-28, the
  USER rulings line "Designation 56→51 CONFIRMED", which lands on main
  under its own ceremony. Checked: that entry is **not present in this
  worktree**, so it is cited as a forward reference and nothing is
  asserted about it here;
- no provenance is re-derived from any other triage row. The comment
  now carries a standing NB naming M-1's scope and this correction, so
  the wrong wording is not reapplied.

**Commit `843d759e`** — trust-adjacent, batched alone. Extraction
re-verified: **OLD extractor 51, NEW extractor 51**, lockstep intact.

### F-2 (MEDIUM) — ci's mirror of the parser, hardened

`scripts/ci:630` carried the **byte-identical un-hardened pattern**,
on the **every-commit** path, under a comment claiming "Extraction
mirrors the judge's" — true before this slice, made false by it.
Hardening one copy and leaving its stated mirror behind is the half-fix
that reads as done and is not.

Applied the same anchored range, **verified byte-identical** to the
judge's; the mirror comment is true again and now cites the 2026-08-27
hazard and F-2 so both are updated together. This leg matters more
than the judge's: it feeds the D4-F2 lockstep check that catches a
one-sided DELETION from the designated list at gate rather than
landmark cadence.

| input | OLD pattern | NEW pattern |
|---|---|---|
| clean `Audit.lean` | 51 | **51** |
| bracket-injected copy | **33** ← hazard | **51** ← defeated |

**Commit `b7e3c8f3`** — trust-adjacent. No gate weakened: the change
makes a fail-closed check harder to blind, not easier.

### F-3 (LOW) — the fail-closed claim, stated exactly

§3's "the surplus names break the lockstep diff, and the run FAILS"
overstated. Re-measured at this tip: **zero `` `` name literals appear
after the list's closing line**, so a never-matched terminator runs to
EOF and still yields **exactly 51**. The guarantee is **"never a
silent SHORT list"**; the surplus backstop engages only if names ever
come to follow the list. Corrected in §3 **and** in the same
overstated comment I had put in `scripts/comparator-judge` — [AGENT]
deviation from the "records only" batching, declared here: leaving a
known-overstated comment in a trust-adjacent file after the audit
flagged the wording is the F-2 mistake again. The edit is **comment
text only**; the range expression is untouched.

### F-4 (LOW) — the diffstat label

§6's figure was presented as `HEAD` but measured at `1022a6c2`.
Relabelled to its true anchor, with the fix round's deltas below.

### F-5 (LOW) — the non-vacuity overstatement

"Why nothing is lost" was false. The retired pair was **the only
discriminating witness for `allStreamsOkPool`**: verified at this tip,
every surviving in-tree use is a `= true` certificate, so there is
**no in-tree demonstration that the checker can return `false`** — its
discrimination is **UNWITNESSED in-tree**, and the deadlock probe
survives only as an archived record. A checker returning `true`
unconditionally would satisfy every live use. Reworded to say exactly
that in all four places: this log's item-4 section,
`docs/ARCHIVE.md`'s fj entry, and
`Specs/GoldenForkJoin.lean`'s `forkJoinAllStreamsCert` docstring
(which now **names the deleted theorem as the retired leg** rather
than silently substituting the fact). The **named re-supplier** is the
corpus's fork/join member when concurrency resumes (plan §5), whose
negative twin restores a live false-witness.

Also fixed under F-5: the registry's `ChoiceCanon` row carried a stale
"2 live (ChoiceInv, SeedCFormLit)" census — **both** consumers were
already dead (ChoiceInv at the 2026-08-27 triage K-3, SeedCFormLit at
the W0 reset), so the row now reads **0 live at deletion**, which is
what the item-1 sweep actually found.

### Fix-round ceremony

**Same posture as the first round**: box-wide build lock taken and
released; `GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=48G scripts/capped
scripts/ci`; judge run bare. Both judged by captured exit code.

| gate | result | evidence |
|---|---|---|
| `scripts/ci` | **`EXIT=0`, RESULT: PASS** | `artifacts/hygiene/ci-fixround.log` |
| `scripts/comparator-judge` | **`EXIT=0`, PASS — 51 theorems in 118 s**, fresh clone @ `09f8f5983f8f` | `artifacts/hygiene/judge-fixround.log` |

The judge was re-triggered because `proofs/Audit.lean` was re-touched
by F-1, and was independently owed by ci's scope note ("2 file(s) in
Challenge's trusted closure changed since that run"). **51 theorems,
like-for-like** with both prior landmarks (51 in 122 s on 2026-08-27,
51 in 117 s at the pre-audit tip) — the designated set did not move in
this fix round either. Marker appended:

```
LANDMARK-RUN: 09f8f5983f8f 2026-08-28 51 118
```

The ci run also exercises **F-2's leg directly**: `ok statement-TCB
closure` is the step whose Audit↔judge-config lockstep now runs through
the hardened extraction, on the every-commit path.

### Fix-round deltas

`git diff --stat 620e1a77..09f8f598` (the fix round proper): **7
files, +239 / −40**, of which 177 changed lines are this log.

| commit | fix | files | flag |
|---|---|---|---|
| `843d759e` | F-1 — designation provenance restored | 1 | **TRUST-ADJACENT, HIGH** (statement-TCB gate file, comment only) |
| `b7e3c8f3` | F-2 — ci parser mirror hardened | 1 | **TRUST-ADJACENT** (every-commit gate; check made harder to blind) |
| `09f8f598` | F-3/F-4/F-5 — record corrections | 5 | records (+ one comment-only touch of `scripts/comparator-judge`, declared under F-3) |

**Cumulative at the final tip** (`05e81b70..09f8f598`): **13 files,
+663 / −749**; excluding this log, **12 files, +202 / −749** — the
slice is still a net deletion of 547 lines of tree, with the 616-line
`ChoiceCanon` kill as its bulk.

### Standing delta-flags for the landing review (superseding §6's list)

1. **Three trust-adjacent commits** across the slice: `4d29aab4`
   (superseded by `843d759e`), `17d23216`, `b7e3c8f3`, plus
   `843d759e`. None changes the designated set, the axiom allowlist,
   the interpreter, or any statement's meaning; all are verified by
   extraction counts and two judge runs at 51.
2. **F-1 was a genuine provenance error by this executor**, caught by
   the audit, not by me. It is corrected in the gate file and recorded
   here with the citation trail; the superseded wording is preserved
   in §2 under a banner rather than quietly overwritten.
3. **The `allStreamsOkPool` evidentiary gap (F-5) is now an open,
   named debt**, not a closed item: the checker's discrimination is
   unwitnessed in-tree until the corpus fork/join member supplies a
   negative twin. A reviewer should treat this as the slice's one
   substantive cost.
4. `GOLEAN_ALLOW_NO_DIFF=1` used in both rounds; scope argument in
   §5a — no runtime code is touched anywhere in this slice.
5. Still **no merge and no push**. Branch-complete at `09f8f598` plus
   this record; both remain the user's calls.
