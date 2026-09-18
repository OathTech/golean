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

---

# B7 — fixed context / mutable store (2026-09-17)

Lane `core/b7-context-store-0917`, branch of the same name, base main
`7f1c1fe7`; the brief is `docs/2026-09-16_b7-context-store-charter.md` with
its §9 decisions RULED ([USER] 2026-09-16, verbatim, relayed: «Yes, let's go
ahead with the D1-8 rulings as recommended (aside from D3)»; D3 PARK ruled
separately); dispatch [USER] 2026-09-17, relayed: «Great, land it, then launch
B7». Handoff: `docs/2026-09-17_b7-context-store-handoff.md`; evidence:
`docs/evidence/2026-09-17_b7-context-store/`. The entries below are in this
log's format (the coordinator's brief asked for them here; the arc's landing
record `docs/2026-09-03_design-hygiene-arc.md` carries the row).

*Quantifier-audit line ([AGENT]): B7 advances NO fidelity quantifier — zero
corpus rows move (the gate's zero drift is THE regression). It advances the
STATEMENT of the semantics: the program context is a parameter of the
relation, not a mutable field, and 48 «the program did not change» proof
sites vanish by type.*

## S0 — census, probe, measurement (records only; commit `fc1aa228`)

Census BEFORE: 38 field-equality conjuncts in `StateWf.lean` statements + 6
in `MultiWfSound.lean` + 4 `htypes` in `MachineSound.lean` = 48 statement
sites (54 atoms in StateWf incl. proof-internal). Reverse-import map of the
five context fields recorded (Ops 24/4/4/1/1, Machine 6/1, StepFn, Race 2 —
the charter's numbers). `fun_cases stepFn s c ch`: 162 arms, fingerprinted.
MEASURED warm after a `State.lean` touch: `lake build GoLean.GoCore` = 104 s
(20 modules, LEAN_NUM_THREADS=4, 32G, under the train's concurrent gate) —
the charter's «≤ 15 min» condition met ×8.5.

## S1 — the records (`ProgramCtx.lean`, `Store.lean`, `State.lean`, `StateWf.lean`, `MachineEqb.lean`)

[AGENT] `ProgramCtx` = D2 (b) (`structure … where program : Program`, five
projections + `globals`), NO platform field (D1 (a)); `ProgramCtx.ofTables`
NEW — the hand-built entry with the OLD `ExecState` defaults (`#[]`
everywhere, fail closed). `Store.lean` = the snapshot `85f9abd7`'s file
(refusal texts byte-preserved; header with provenance). `StateWf` heap-only:
`Store.locSup σ := Heap.locSup σ.heap`; the A4 debt retired with NEW zero
lemmas `Expr.locSup_eq_zero`/`Stmt.locSup_eq_zero`/`Func.locSup_eq_zero`/
`funcListSup_eq_zero` (functional mutual induction). **D6**: `MachineWf σ c :=
StateWf σ ∧ ConfigWf σ.nextAddr c` — the vacuous `itersNormalized` conjunct
DELETED (a theorem-statement change, flagged); `step_preserves_iters` retired.
`Store.eqb` compares the heap only. The 38 StateWf conjuncts deleted from the
statements; every consumer re-indexed (five compiler-guided rounds).
Explicit-target builds EXIT=0 throughout.

## S2 — the sequential machine (`Ops`, `Machine`, `StepFn`, `MachineSound`, `UnseqSound`)

[AGENT] `variable (ctx : ProgramCtx)` for definitions; theorems take `ctx`
IMPLICITLY (`variable {ctx}` toggles) so lemma applications stay as they were
— the alternative (the snapshot's explicit ctx on theorems) named and not
taken. 43 Ops context readers + 10 Machine helpers + 2 no-param helpers lose
the store (the core build must be warning-free). `stepFn ctx s c ch`,
`Step ctx`, `Steps ctx`; `runProgramSetupM` builds and RETURNS the run's
context. The 4 `htypes` hypotheses gone (`structTagCompatible_congr` retired
as `htypes ▸ rfl`). `enterFramePick_of_isSome_false` quantifies the store
after the family test (binder order). Coherence theorems `stepFn_sound`,
`step_complete`, `step_complete_any_wf`, `stepFn_consumption_none/some`
restated with `ctx`, re-proved, 0 positional tags moved (S2 probe: 162 arms,
identical tags/order/fingerprints, +1 hypothesis each). Builds EXIT=0, 0
warnings.

## S3 — pool, traces, detector (`Race`, `Multi*`, `NPDRF`, `Trace`, `PoolTrace`, `ProgramTrace`, `AbortObservation`, `StringPanic`, `Enum*`)

[AGENT] D4 (a): `MultiConfig.shared : Store`, threads/cur untouched;
`StepM ctx`, `StepE ctx`, `MultiWf ctx m` (the pool keeps its `itersNormalized`
conjunct — D6 named `MachineWf`; the pool twin is PENDING [USER], handoff §8).
The 6 `MultiWfSound` conjuncts deleted, consumers re-indexed (two rounds).
`ProgramRun` stays PROGRAM-level (binds the setup's context). Footprints
byte-identical: `Race.stepAccesses ctx s c` is the former function over
`Store`; `dispatchAccesses`/`deferEntryAccesses` context-only.
`lake build GoLean.GoCore` EXIT=0 (33 jobs).

## S4 — enumerator and CLI (`EnumDedup.lean`, `CLI.lean`, `ChoiceTrace.lean`)

[AGENT] `EnumProgram.ctx` built ONCE by `CLI.enumSetup` (`⟨program⟩`); the
explorer's `ExpCtx` reaches it as `ctx.ep.ctx`; `buildCert ctx`/`checkCert
ctx`. WIRE-NEUTRAL by construction: `NativeToIR.lean` untouched (the decoder
yields the same `Program`; the context wraps it). Default `lake build` (lib +
exe) EXIT=0 under the box lock.

## S5 — tests, then THE gate

[AGENT] 13 hand-built `ExecState` fixtures in `Tests/GoCoreEval.lean` →
`ProgramCtx.ofTables` (old defaults preserved), `emptyCtx` for the old
`({} : ExecState)`; `GoCoreContract`'s ∀-state facts take `{ctx}` implicitly,
its concrete runs use `exampleCtx`/`emptyCtx`; `MethodIdentity`,
`PanicRendering`, `StringPanicMembers` re-fixtured. Every `Tests.*` module
EXIT=0. Whole-corpus choice trace (main's binary vs B7's, the two wave-3
exclusions): BYTE-IDENTICAL — 23,679 consumption records, identical sha256,
identical validator summaries. Gate: EXIT=1 (1068 s): 3676 cases 3427 PASS / 249 expected FAIL, 394 negatives, eval 211/0, every step ok EXCEPT the two EXPECTED 5a-class items (certificate provenance STALE — compiled inputs `GoLean/CLI.lean`; the ONE cached certified row `imported-goose/channel/google-search` judged stale for that reason); no other row moved

### Refusal-text change, disclosed

The post-seed assertion's `.internal` text at BOTH seams (`runProgramSetupM`,
`CLI.enumSetup`) drops «or function body» — the check is heap-only now and a
message naming an unperformed check would be a fail-noisy lie. Unreachable on
decoded programs (A4). The [USER] may prefer byte-preservation (handoff §8.4).

## Fix round — the pool-side `itersNormalized` conjunct (2026-09-17)

[USER] Mike, 2026-09-17, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «We should delete the vacuous conjunct right? that's just a strict improvement. The rewordings sound fine. Agree with the audit, go ahead and launch (after the rulings if relevant)». [AGENT] fix-round worker, runtime commit `1fafc9f2`
(after a clean rebase onto main `5955e55f`: `2500b434 → 73ad798d`).
**Theorem STATEMENTS changed (a restatement, flagged, as D6 required for
`MachineWf`; nothing weakened — every deleted conjunct/hypothesis was
identically `true`):** `ThreadWf bound t` (the `types` parameter and the
`Config.itersNormalized types c = true` conjunct deleted), `MultiWf m`
(CONTEXT-FREE: the conjunct was its only reader of `ctx.types`), both
`Decidable` instances; in `MultiWfSound.lean` 18 theorems — `ThreadWf.running`,
`ThreadWf.aborted`, `ThreadWf.mono`, `spawnStep_wf`, `resumeRecvDelivery_wf`,
`selectRecvDelivery_wf`, `resumeThread_wf`, `pool_get_wf`, `pool_set2_wf`,
`chanArrivalPlan_wf`, `arrivalCases_single_wf`, `arrivalCases_multi_wf`,
`applyPairing_wf`, `pool_set1_wf`, `pool_set1_aborted_wf`, `pool_set_push_wf`,
`stepThread_wf`, `stepMulti_wf` — lose 15 hypothesis binders, 10 conclusion
conjuncts, 13 `{types : TypeEnv}` binders and 16 internal `have`s (the handoff
§4 «Fix round» says which per theorem). **Deleted, tombstoned (16
declarations):** `Cont.itersNormalized`, `Config.itersNormalized`, their `_true`
certificates, the 11 `*_itersNormalized` walk/transparency lemmas in
`StateWf.lean`, `spawnPlan_iters`. Nothing outside `GoLean/GoCore` named any of
it (docs only), so nothing stayed; `MultiSound.lean` never named `MultiWf`.
`MachineSound.lean`: one history comment gains a closing parenthesis.
Sequential warm StateWf 19 s / Multi 5 s / MultiWfSound 76 s / `GoLean.GoCore`
16 s — every EXIT=0 on the FIRST round, 0 warnings. Gate: `scripts/ci --diff`
EXIT=1 (934 s): 3676 cases 3427 PASS / 249 expected FAIL, 394 negatives, eval
211/0, every step ok EXCEPT the same two EXPECTED 5a-class items (certificate
provenance STALE — compiled inputs `GoLean/CLI.lean`; the ONE cached certified
row `imported-goose/channel/google-search` judged stale for that reason); no
other row moved. Choice trace (the SAME main binary the lane used, re-run,
vs the fix-round binary, plus the lane's original main dump): BYTE-IDENTICAL —
23,679 records, one sha256 `5f901024…58b5a` on all three sides, `cmp` EXIT=0.
Items (3)/(4) of the handoff §8 (the two refusal-text rewordings) RULED as
landed («The rewordings sound fine») — no change.

## Audit fix round — the F1 literal revert and the F7 dead context (2026-09-17)

[AGENT] fix-round-2 worker, lane `core/b7-context-store-0917`. The pre-merge
adversarial audit (`docs/2026-09-17_b7-context-store-audit.md`, branch
`review/b7-context-store-0917` at `b51bc5c4`) returned **FIX-FIRST, narrow and
records-class** — 10 findings, none at WRONG-ANSWER / UNSOUND-PROOF / WEAKENING
/ COHERENCE-GAP / FAIL-OPEN severity, none gate-weakening. Authority: [USER]
Mike, 2026-09-17, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «Agree with the audit, go ahead and launch». Dispositions in full:
handoff §13; the two PENDING [USER] items in `docs/2026-08-31_qrow-rulings.md`
(«The B7 audit fix round»).

**Runtime, two files, +5/−42; NO theorem statement changed, no definition
changed, no semantic change, no wire change:**

- **F1 (REVERT).** `GoLean/GoCore/Machine.lean:3734`, `applySyncOpCore`'s
  defensive `.internal`: a mechanical `applySyncOp ` → `applySyncOp ctx ` pass
  had rewritten the inside of the STRING («… apply through applySyncOp ctx (the
  choice-taking entry) …»), undisclosed. Restored to the pre-B7 bytes; the line
  is now byte-identical to `5955e55f:GoLean/GoCore/Machine.lean:3700`. So the
  branch's refusal-text change set is exactly the TWO disclosed, RULED
  rewordings (the post-seed assertion at both setup seams) plus the
  byte-preserved `Store.updateCell` text — as the handoff always claimed.
  Independent re-verification here (a literal extractor over all 34 changed
  files, both revisions, interpolation arguments normalised): exactly three
  content-changed literals, no fourth accidental one. The [USER]'s alternative
  (disclose-and-keep) is recorded and still open at the merge ask.
- **F7 (dead code).** `GoLean/GoCore/MachineEqb.lean`: `variable (ctx :
  ProgramCtx)` and its 37 `variable {ctx}` / `variable (ctx)` toggles DELETED
  (38 lines). The module named `ctx` in no definition and no theorem — the
  idiom had been copied from the modules that DO read the context, while
  `Store.eqb` is heap-only. A pure removal of a binder nothing bound: not one
  statement re-types. The stale header comment is replaced by an accurate one.

Sequential warms, captured exits, `LEAN_NUM_THREADS=4 GOLEAN_MEM_MAX=32G`
through `scripts/capped`, complete (not representative): `GoLean.GoCore.MachineEqb`
EXIT=0 (96 s, 25 jobs — the rebuild of `Machine` and dependents that the F1 edit
triggers, included) · `GoLean.GoCore` EXIT=0 (1 s, 33 jobs) — 0 warnings in both.

**Records (the same round, second commit):** handoff §1 delta corrected to
34 files / +3,232 / −2,862 (F2); §3's `ExecState` row to 31 files, 29 with code
mentions (F3); ONE spelling of the `itersNormalized` count — 198 lines in
`GoLean/` at `5955e55f`, derivation `git grep -c itersNormalized 5955e55f --
GoLean`, AFTER 13 all prose (F4); the first gate's 1068 s marked «from the
lane's log, tail not tracked» (F5); `spikes/i1-declarations` recorded DARK under
the charter's D7 shape, untouched (F6); the SECOND removed cost recorded — the
setup `StateWf` decision no longer walks function bodies — beside the measured
`Store.eqb` win (F9); the warm-line shortfall against the charter's «every»
acknowledged rather than defended (F10); F8 posed PENDING [USER] with the
[AGENT] recommendation to accept the one-context specialisation.

# C1 — the memory module and the access trace (lane `core/c1-memory-module-0918`, base main `68b261e6`)

Charter: `docs/2026-09-17_c1-memory-module-charter.md` (§7 D1–D7, D9, D10 RULED by default
acceptance 2026-09-18; D8 RULED [USER] 2026-09-18 «deprecate/mark unsound, not delete»).
Evidence: `docs/evidence/2026-09-18_c1-memory-module/README.md`. Handoff:
`docs/2026-09-18_c1-memory-module-handoff.md`.

## S0 — records, the §5 spike, the D8 marker, the D10 wording (2026-09-18)

[AGENT] Census at the fork by recorded grep (matches the charter: `loadLoc ctx`/`storeLoc
ctx` call lines Machine 18/29, StepFn 1/1, Multi 2/4, Race 2/0, Ops 4/0; the table family
54/6/5; 13 non-proof alloc sites; 17 `deliverS` apply/entry sites + the pool's
`Thread.afterStep s` + the drivers' `raceUpdate ctx m.shared m.threads` = cost B's
retention set). Write-then-panic audit of every apply arm (delegated read, verified
against the noPanic theorem family): **N 118 / V 46 / W 8**; the W arms are `storeMany`
(dead), `.allocNew`/`.makeSlice`/`.makeMap`/`.makeChan` (alloc before the target's
`valueAsLoc`/path store — `.makeMap`/`.makeChan` in their hint-/cap-less forms are
REACHABLE through `stepFn`: a nil target panics after the payload alloc, the arrival
nil-check is skipped at one operand), `.clearSlice`/`.copySlice`/`.appendSlice` element
loops (a later element's bound; needs a header/backing inconsistency `validateSlice`
does not exclude). Benchmark BEFORE reproduced (write_fixed 21 µs → 107 ms across m;
append_grow 4,000 = 30.4 s; alloc_new 32k = 13.8 s; (h) scalar phase 0.237 → 6.37 s;
246 ns/step). **Spike PASS**: `spikes/c1-frame/Frame.lean` EXIT=0 — (a) `arraySet_comm`,
`fieldModify_comm`; (b) `isNormalForTyTy_array_set`, `isNormalForTyAt_struct_set`; (c)
F1/F2 stated; `f1_canon` PROVED at every depth for the CANONICAL (typeId-erased)
relation. Three findings, none about the representation: F1 as chartered (structural
`ShadowKey.overlap`) is FALSE on tag-compatible field aliases — **BUG-111** filed,
PENDING [USER] (a missed race, fail-open); F1 is agreement on SUCCESSFUL loads, not
`Except` equality (wrong-base refusal texts embed the value); `Array.findIdx?` does not
kernel-reduce — the module's field search must be structural. D8: `NPDRFReduction`
carries `@[deprecated … (since := "2026-09-18")]` + a banner quoting the ruling; zero
use sites (confirmed by grep; 0 build warnings). D10: `Store.updateCell`'s `.internal`
names `Store.alloc` (pinned nowhere else). Warm after the `Store.lean` touch:
`GoLean.GoCore` EXIT=0 in 105 s (33 jobs, 0 warnings). Gate: `scripts/capped scripts/ci
--diff` EXIT=1 (938 s): 3676 cases 3427 PASS / 249 expected FAIL, eval 211/0, every step ok
EXCEPT the two EXPECTED 5a-class items (certificate provenance STALE — compiled input
`GoLean/GoCore/NPDRF.lean`; the ONE cached certified row `imported-goose/channel/google-search`
judged stale for that reason); no other row moved.

## S1 — the module and cost A (2026-09-18)

[AGENT] ONE gated runtime commit (SHA in the handoff). **The module** lives in
`GoLean/GoCore/Ops.lean` beside the normalizer it needs (the charter's «`Mem.lean` or
`Store.lean` grown»: `Store.lean` keeps the representation, `allocCell`, `updateCell`
and the payload readers/writers; the value-cell operations — `Store.alloc`, `loadLoc`,
`storeLoc`, the write path, `HeapNormal` — are the Ops section «The memory module's
write path»). **Cost A fixed in place**: `storeLoc` is ONE root-cell update whose new
cell is the ROOT-FIRST in-place write `writeAt` — `Loc.rootPath` (leaf-first `Loc` →
root + path), `Ty.stepDown` (the DECLARED type one step down, `.defined` hops
decrementing the bound exactly as `normalizeValueForTyAt` does), the incoming leaf
normalized at the descended `(type, bound)` (so the result is byte-identical to the
former whole-root re-normalization on every normal cell), `Array.modifyM` at every
level (the element taken out while rebuilt), a STRUCTURAL field search `fieldIdx?`
(S0 finding 3: `Array.findIdx?` does not kernel-reduce). `normalizeListWith` /
`normalizeFieldsWith` are LINEAR (accumulator form, same names and signatures; the
old recursive equations are lemmas `normalizeListWith_nil/_cons`,
`normalizeFieldsWith_nil_left/_nil_right/_cons`, so every proof that unfolded them
keeps its shape). **D3**: `Store.alloc ctx s v ty : Except Stop (Loc × Store)`
NORMALIZES (13 call sites, the `Step.initialization` premise restated to `= .ok (loc,
s')`); `HeapNormal ctx s` (every value cell `isNormalForTy` at its declared type;
payload cells vacuous; `Heap.normalB` structural, decidable) is a `StateWf`
conjunct — `StateWf ctx σ := Store.locSup σ ≤ σ.nextAddr ∧ HeapNormal ctx σ`; hence
`MachineWf ctx σ c`, `MultiWf ctx m` (context-free since the B7 fix round; the type
table decides normality, so the context returns — a RESTATEMENT, flagged, nothing
weakened: every theorem concluding `StateWf` now proves MORE), `StmtOpPres ctx σ σ'`.
`step_preserves_wf` re-proved through the helper family: `HeapNormal.of_updateCell /
of_allocCell / of_alloc / of_storeMapPayload / of_storeChanPayload / of_storeLoc /
of_storeMany`, the leaf congruence `writeAt_isNormal` (+ `_array`, `_struct` at the
index layer), idempotence `normalizeValueForTy_isNormal` (type + index layers; leaf
kinds `IntKind.normalize_idem`, `FloatKind.normalizeBits_idem`), `defaultValue_isNormal`
/ `defaultValue_normalize` (the zero values `allocDecls`/`seedGlobals`/`makeSlice`
allocate re-normalize to themselves), `buildAppendBackingValue_normalize` (the spill
backing re-normalizes to itself — what `applyStmtOp_appendSlice_congr` now needs to
push the ∀-choices class through the normalizing alloc). `storeLoc_shape` (via
`writeAt_locSup`), `storeLoc_congr` (via `writeAt_congr`), `storeLoc_root_frame`
(one `updateCell_lookup_ne` step), `storeLoc_base_noPanic`,
`storeLoc_noPanic_of_loadLoc_ok` (via the root-first read bridge `readAt` /
`loadLoc_eq_readAt` and the `fieldIdx?` ↔ `StructFields.lookup` bridge) — STATEMENTS
UNCHANGED, proofs re-derived. `allocCell_wf` gains the payload-normality hypothesis
(callers pass `rfl`). Refusal texts byte-preserved (load texts on prefix steps, store
texts on the last, as the former recursion produced them); TWO disclosed class changes
on unreachable paths: a PATH store into an unbound root is now `Store.updateCell`'s
`.internal` (was `loadLoc`'s `.stuck "unbound…"`; unreachable by heap density), and the
leaf-type descent's NEW named `.stuck`/`unsupported` refusals (a cell whose declared type
has no component where its value has one — impossible under `HeapNormal`; e.g. a field
store through an interface-typed cell, which typed Go cannot express). `arraySet` and
`StructFields.set` left the write path and have NO code caller; their lemma families
(`arraySet_locSup/_congr/_ok_of_arrayGet_ok`, `StructFields.set_locSup/_congr/_noPanic`)
are dead — DELETION DEFERRED to S2 (which re-gates these files), recorded as an owed
tombstone. `Tests/GoCoreContract.lean`'s `address_bound_admits_ill_typed` decides
`StateWf` at a concrete context (the `.bool` slot's ill-typed `int` is still admitted:
the normalizer does not coerce there). Checkpoint gate at the representation change
alone (before the conjunct): `ci --diff` EXIT=1 (720 s): 3676 = 3427/249, red ONLY on
the expected 5a pair — `alloc`-normalizes moved NO row (D3's referral clause not
triggered). S1 GATE: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock (09:06:02–09:17:37 UTC): **EXIT=1, 695 s**; **3676 cases: 3427 PASS / 249 expected FAIL**; `eval tests` 211 ok; `core build (warning-free)` ok; `core totality audit` ok; `frontend pins` ok; `wire boundary` ok; every other step ok. RED: exactly the two 5a-class items — `certificate provenance` (C9 HIGH: «STALE certification: changed dependency build/files/GoLean/CLI.lean») and `baseline diff (DRIFT)` with the SINGLE line `imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` — the one cached certified row, judged stale because compiled semantic inputs changed. ZERO other drift. Tail: `gate-tail-s1.txt`. Whole-corpus choice trace (`scripts/choice-trace-corpus --dump --jobs 6 --exclude goroutines/send-then-spin --exclude strings/trimspace-repeat/repeat-bound-refused`, main `68b261e6`'s certified binary `231df9a9…` vs the S1 binary `f462cf50…`, run 09:23–09:41 UTC): sorted dumps `cmp` **EXIT=0 — BYTE-IDENTICAL**, 23,685 consumption records both sides, one sha256 `70e12e023f3ee30b9d71317454e11dedcb6c6ec039d63aeddfbb3d4906aceb57`; 34 frontend-refusal exports and the 2 exclusions identical; each tracer run EXIT=1 for the SAME pre-existing «FINDINGS present» depth listing (main 609 s, S1 436 s). Tails: `trace-summary-main-s1.txt`. Benchmarks: `.tmp/golean-s1` = the gated binary (sha256 `f462cf50…48f3`), same frontend and probes as BEFORE; `--plan full`, 3 runs per point, medians, net of the empty probe (0.0213 s); run 09:18–09:23 UTC (the whole plan in 337 s — BEFORE needed 28 min), load1 ≈ 1.3, no sibling build. Artifacts: `bench-after-s1.json`, `bench-after-s1-summary.md`.

**S2a (2026-09-18, gated) — the DATA trace, both accounts live, the trace-equality
audit.** The access vocabulary (`AccessKind`, `ShadowKey`+`overlap`, `locPrefix`/`locOverlap`,
`SyncWordName`) moved from `Race.lean` into the module (`Ops.lean`); `Access`/`AccessTrace`;
the EMITTING operations `Mem.load`/`loadFor`/`store`/`mapRead`/`mapWrite`/`loadElems`/
`storeElems`/`loadRun`/`storeRun`/`loadSlice` as wrappers over the S1 primitives (which keep
their types as the module's peek/raw writers); `loadResults` beside the drivers' `loadMany`;
`dynamicDispatch?` emits the receiver read at `dispatchLeaf`; `projChainTarget` moved to
`Machine.lean`. Every emitting helper returns its trace as the last ok-component;
`deliver`/`deliverS` carry it (panic → `[]`); `applyStrictOp` takes `leafOf` (`.deref`'s
narrowing, the caller's `projChainTarget`); `stepFn`'s FOURTH component; `Step` LABELLED (122
constructors: 94 × `[]`, 28 by their operations); `StepE`/`StepM`/`StepMFine` labelled, the
closures erase; `StepEvent.trace` (a goroutine step: `stepFn`'s; a spawn: the child's entry
read; pool-own steps `[]`). Coherence RE-PROVED with the label: `stepFn_sound`,
`step_complete`, `step_complete_any_wf`, `stepFn_consumption_none/_some`, `stepFn_oblivious`,
`stepMulti_sound : … → StepM ctx m m' ev.trace`, `stepM_complete … ∧ ev.trace = tr`,
`step_preserves_wf`; StateWf/MachineSound/MultiSound/MultiWfSound/MultiStreams/
EnumDedupSound/UnseqSound/Trace/AbortObservation/PoolTrace/NPDRF restated. Mirrors
(`appendSpill?`, `EnumDedupCheck.appendApplyNoSpill`) read through `Mem.loadSlice`.
`raceUpdate` UNCHANGED (zero detector drift by construction). Disclosures: `mapDelete` of an
absent key rewrites the unchanged payload so the write is emitted (gc instruments it
unconditionally); two UNREACHABLE refusal texts moved to `Mem.storeRun`/`loadRun`'s
(`sliceIndexLoc`'s text); `sliceVisibleValues` over the structural `Mem.loadElems`. THE AUDIT
(the tracer, per step, both accounts as multisets under `raceUpdate`'s recording rule; new
TSV columns `traceMismatches`/`firstTraceMismatch`, every mismatch also an alarm): whole
corpus, **21,835 (row, stream) results, 0 mismatches**; the raft twin's five probe entry
points 30/30 (row, stream) results ok, 0 mismatches, choice trace byte-identical vs main (14,360 records, `cmp` EXIT=0); choice trace byte-identical vs main (23,685 records, sha
`70e12e02…eb57`, `cmp` EXIT=0; the one pre-existing ERROR finding identical modulo path).
Positive control in `trace-probe-s2a.txt`. Gate: `GOLEAN_MEM_MAX=32G scripts/capped scripts/ci --diff` under the box-wide lock
(11:17:29–11:29:48 UTC): **EXIT=1 in 739 s**, 3676 cases 3427 PASS / 249 expected FAIL, `eval
tests` 211 ok, core build warning-free, red ONLY on the expected 5a pair (`certificate
provenance` STALE on `CLI.lean`; the one cached certified row `imported-goose/channel/
google-search`), ZERO other drift (`gate-tail-s2a.txt`). Owed to S2b: the dead
`arraySet`/`StructFields.set` + six lemmas (tombstones), the module-docstring peek list
(kept in the evidence README this slice), `accesses_eq_stepAccesses`, the table deletion.
Evidence: `docs/evidence/2026-09-18_c1-memory-module/` (`trace-audit-s2a.txt`,
`trace-probe-s2a.txt`, `gate-tail-s2a.txt`).

| probe / point | BEFORE net | AFTER (S1) net | S1 target | verdict |
|---|---:|---:|---|---|
| `write_fixed(m, 100)` per write, m = 10 / 100 / 1,000 / 3,000 / 10,000 | 21 / 44 / 1,248 / 9,560 / 106,972 µs | −2 / 1 / 3 / −2 / **16 µs** (100 writes sit at the 21 ms startup noise floor; the count-varying rows put one write at 13.1 µs (m = 10, w = 1,000) / 12.6 µs (w = 10,000)) | flat: within 2× across m | **MET** (12.6 → 16 µs, ≈1.3×, at noise level; the BEFORE 5,000× slope is gone) |
| `append_grow(n)` net, n = 250 / 500 / 1,000 / 2,000 / 4,000 | 0.023 / 0.113 / 0.700 / 4.56 / 30.42 s | 0.0056 / 0.0141 / 0.0352 / 0.1001 / **0.2748 s** | n = 4,000 < 2 s | **MET** (111×) |
| `append_grow` successive ×2 ratios | ×5.0, ×6.2, ×6.5, ×6.7 | ×2.5, ×2.5, ×2.8, ×2.7 | ≤ 2.2 | **MISSED** — a residual super-linear term: each in-place append still copies the backing once (the heap is shared across the step — cost B, S3's), ≈ Σ cap; plus the spill path's linear rebuilds |
| `scalar(80000)` per step | 246 ns (0.964 s net) | 250 ns (1.001 s net) | within 10 % | **MET** (+3.9 %) |
| `struct{a [10000]byte; x int}: s.x = i` per write | 109,130 µs | 5 µs | (cost A witness) | quadratic gone |
| `[10000]byte: b[0] = v` per write | 107,972 µs | 23 µs | (cost A witness) | quadratic gone |
| `append_cap(6400, 100)` per in-place append | 44,437 µs | 29 µs | (cost A witness) | quadratic gone |
| `alloc_new(32000)` net | 13.77 s | 13.51 s | (S3) | unchanged, as expected |
| (h) scalar phase at h = 0 / 40k live cells | 0.237 / 6.37 s | 0.259 / 6.05 s | (S3) | unchanged, as expected |
| `read_fixed(10000, 1000)` per read | 17.8 µs | 16.7 µs | (control) | flat |
| `map_write(4000)` per write | 45 µs | 45 µs | not a C1 target | unchanged |

Reading: cost A (the whole-root re-normalization with the quadratic `#[head] ++ tail`) is gone — every per-root-size slope is flat to the noise floor. The two misses named above are the SAME mechanism, cost B (the pre-step store retained across the step makes the root array shared, so `Array.modifyM` copies it once per write — O(m), the linear term the BUG-090 note predicted); S3 removes the retention..
