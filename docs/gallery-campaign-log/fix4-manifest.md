# Fix round #4 — edit manifest

Every edit made in fix round #4, written as the edit is made. The operator
verifies THIS FILE against the tree. An edit absent from this manifest is a
defect.

Base tip: `3a6218cb` (branch `gallery-campaign`, tree clean at start apart
from four untracked `proofs_GoLeanProofs_Examples_Histogram_*.lean` scratch
files at the repo root, which are NOT touched — they predate this round).

Rules in force, unchanged from round #3: (R1) nothing off the enumerated
list is touched; (R2) no cite/number/claim is corrected until the CURRENT
text has been PROVEN wrong, with the derivation run for BOTH old and new
value; (R3) every edit is recorded below with file | line | old | new |
derivation | output.

**New this round (R4): THE CITE CONVENTION.** Line-cites in mutable campaign
docs are either UNIT/SECTION-ANCHORED (`g1.md §Unit G1.7b`; `the E6 walk in
g2.md §"THE E6 REGISTER WALK"`) or COMMIT-QUALIFIED (`g2.md:868 @
53a44689`). Bare tip-relative line numbers are retired for cross-doc
references. In-file cites to stable code lines in COMMITTED Lean sources
remain fine. Applied to every cite touched this round; recorded as one line
in `docs/gallery-campaign-log/INDEX.md` §"What the log is".

---

## F-1 (MATERIAL) — the gateway attribution: `FibMemo/Rec.lean`, `wp-library-design.md`

### The derivation, run fresh this round

Script written from scratch for this round — `.tmp/fix4-closure.py` — NOT a
reuse of round #3's `.tmp/irisdep.py`, so round #3's output is a cross-check
rather than the source. Module `A.B` is resolved against two source roots
(`proofs/` for `GoLeanProofs.*`, the repo root for `GoLean.*`); `Iris.*` is
the marker and is never followed.

```
$ python3 .tmp/fix4-closure.py
Examples modules: 132
transitively import Iris: 63
Iris-free: 69

modules in an Iris-reaching closure that DIRECTLY import Iris:
  GoLeanProofs.Ghost                                 63
  GoLeanProofs.HeapBridge                            63
  GoLeanProofs.Lang                                  63
  GoLeanProofs.Laws.Eval                             63
  GoLeanProofs.Lifting                               63
  GoLeanProofs.Tactics.GoWalk                        63
  GoLeanProofs.Laws.StmtOps                          62
  GoLeanProofs.Adequacy                              1
  GoLeanProofs.Laws.Assign                           1
  GoLeanProofs.Laws.Call                             1
  GoLeanProofs.Laws.Control                          1
  GoLeanProofs.Laws.Init                             1
  GoLeanProofs.Laws.Loop                             1
  GoLeanProofs.SurfaceExit                           1

present in ALL 63 closures: 6
  GoLeanProofs.Ghost
  GoLeanProofs.HeapBridge
  GoLeanProofs.Lang
  GoLeanProofs.Laws.Eval
  GoLeanProofs.Lifting
  GoLeanProofs.Tactics.GoWalk

GoLeanProofs.Laws.StmtOps in closure of: 62 / 63
  NOT containing it: ['GoLeanProofs.Examples.Fib']
  StmtOps directly imports Iris? True  imports=['Iris.ProgramLogic.WeakestPre', …]

  import GoLeanProofs.Laws.StmtOps DIRECTLY: 20
  reach it via a sibling: 42

GoLeanProofs.Examples.FibMemo.Rec: closure size (incl. self) = 28, reaches Iris = False
```

**Robustness check on the derivation itself.** The parser stops at the first
non-import line; two repo files lead with a `/-!` block (`Stein/Pure.lean`,
`WordFreq/Pure.lean`), so a variant that greps `^import` over the WHOLE file
was run and diffed:

```
$ diff <(python3 .tmp/fix4-closure.py) <(python3 .tmp/fix4-closure-robust.py)
    (no output)  -> IDENTICAL; both leading-comment files have zero imports
                    (`grep -n '^import' … ` returns nothing for both)
```

**Cross-check against round #3's own output** (`.tmp/fix3-manifest.md:419-421`):
round #3's script printed `gateway … GoLeanProofs.Ghost 62 / GoLeanProofs.Adequacy 1`
— i.e. ONE representative gateway per example, summing to 63, and the
representative it named was **`Ghost`, not `StmtOps`**. So round #3's prose
("the gateway in every case being `Laws.StmtOps`") did not follow even from
round #3's own evidence; its "second hop histogram" line
(`StmtOps 20 (+43 reaching it via a sibling)`) is where the `43` came from,
and 20+43=63 silently absorbed the one example that never reaches `StmtOps`.

### What is TRUE (the four corrections)

1. 63 of 132 Examples modules transitively import Iris — **unchanged, correct**.
2. `Laws.StmtOps` is in **62** of the 63 closures, not all 63. The exception
   is `GoLeanProofs.Examples.Fib`, which reaches Iris through
   `Laws.Assign/Call/Control/Init/Loop`, `SurfaceExit` and `Adequacy`
   (`$ python3 .tmp/fix4-closure.py detail` → `Fib imports: […, 'GoLeanProofs.Laws.Control', …]`,
   no `Laws.StmtOps`).
3. The split is **20 direct / 42 via a sibling / 1 not at all**, not 20/43.
4. There is **no unique gateway**: six DIRECT Iris importers — `Lifting`,
   `Lang`, `HeapBridge`, `Tactics.GoWalk`, `Laws.Eval`, `Ghost` — appear in
   **all 63** closures.

### NOT changed, and why (R2: not provably wrong)

`Rec.lean:1368` "**29 modules, zero under `Iris.`**". My repo-module count is
28 including the file itself; the closure also contains exactly one external
module, `Std.Data.ExtTreeMap`, which is not under `Iris.` — 28 + 1 = 29 under
a "every module in the closure" reading. Both readings agree on the load-
bearing half ("zero under `Iris.`"), so the figure is not provably wrong and
is left alone. Flagged here only so the next reader does not re-litigate it.

### Edit F-1a

| field | value |
|---|---|
| file | `proofs/GoLeanProofs/Examples/FibMemo/Rec.lean` |
| lines | 1377-1386 |
| old text | `**NB — corrected 2026-08-16, fix round #3.** … the gateway in every case being `GoLeanProofs.Laws.StmtOps`, whose first line is `import Iris.ProgramLogic.WeakestPre` (20 example modules import `Laws.StmtOps` directly; the other 43 reach it through a sibling).` |
| new text | attribution replaced by the derivation's actual truth (62/63, the `Examples.Fib` exception, the 20/42/1 split, the six universal direct importers, no unique gateway), plus the one-line `b5f0893c` commit-message errata |
| derivation | `.tmp/fix4-closure.py` (above), robustness diff, round-#3 cross-check |
| output | as shown above |

### Edit F-1b

| field | value |
|---|---|
| file | `docs/2026-08-16_wp-library-design.md` |
| lines | 246-255 (the `>`-quoted VERBATIM copy of the Rec.lean docstring) |
| old text | the same round-#3 sentence, quoted |
| new text | re-synced to Rec.lean character-for-character (the quote is declared verbatim in the file's provenance header, so it MUST move with the source) |
| derivation | same as F-1a |
| output | same |

### Edit F-1b′ — CONSEQUENTIAL (caused by F-1a, therefore in scope)

F-1a lengthened the `unorm_idem` docstring, so the note's cite of that
docstring's extent moved. This is an in-file cite into a committed Lean
source (the convention leaves those alone) but it must track my own edit:

```
$ awk 'NR==1359||NR==1404' proofs/GoLeanProofs/Examples/FibMemo/Rec.lean
/-- Idempotence of the uint64 normal form (Int.emod stability).
not audit-round work. -/            <- docstring now ends at :1404, was :1392
```

| field | value |
|---|---|
| file | `docs/2026-08-16_wp-library-design.md` |
| line | 228 |
| old text | `` `proofs/GoLeanProofs/Examples/FibMemo/Rec.lean:1359-1392` `` |
| new text | `` `proofs/GoLeanProofs/Examples/FibMemo/Rec.lean:1359-1404` `` |
| derivation | the `awk` above |
| output | as shown |

### Edit F-1c

| field | value |
|---|---|
| file | `docs/2026-08-16_wp-library-design.md` |
| line | 272 (§"Designation-relevant input") |
| old text | `the example tree is *already* half Iris-dependent through `Laws.StmtOps`` |
| new text | `… half Iris-dependent — through `Laws.StmtOps` in 62 of the 63 closures and through six always-present direct importers in all 63` |
| derivation | same as F-1a |
| output | same |

---

## F-2 — the four round-#3-authored cites that were stale on arrival

**Why they are stale (one derivation, all four).** Round #3 computed them at
its base tip `53a44689` and then its OWN edits moved the lines:

```
$ for c in 53a44689 3a6218cb; do echo "$c g1=$(git show $c:docs/gallery-campaign-log/g1.md|wc -l) g2=$(git show $c:docs/gallery-campaign-log/g2.md|wc -l)"; done
53a44689 g1=4075 g2=1258
3a6218cb g1=4127 g2=1274
```

Per R4 each is repaired by ANCHORING (or commit-qualifying), never by
repointing to a fresh absolute line.

### F-2a — `g2.md:988`, the cite `(:868)`

R2 proof, BOTH values:

```
$ git show 53a44689:docs/gallery-campaign-log/g2.md | sed -n '868p'
import . "strings"     "stuck": "GoCore function not found: Fields"   (the pre-existing dot-import gap, …)

$ sed -n '868p' docs/gallery-campaign-log/g2.md
IDEOGRAPHIC separators, on the U+200B negative pin, and on undecodable      <- unrelated prose

$ grep -n 'import \. "strings"' docs/gallery-campaign-log/g2.md
756: … 879: … 1060: …          <- the row is now :879
```

WRONG at tip, right when written ⇒ anchor it.

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g2.md` |
| line | 988 |
| old text | `` (`:868`) `` |
| new text | `` (§"E5 — BUILT", the fail-closed-remainder table) `` |
| derivation | the three commands above |
| output | as shown above |

### F-2b — `g2.md:1260`, the cite `(:1115, §"THE BOUNDARY, probe-verified AFTER the build")`

R2 proof, BOTH values:

```
$ git show 53a44689:docs/gallery-campaign-log/g2.md | sed -n '1115p'
1. **E3's boundary paragraph** (§"THE BOUNDARY, probe-verified AFTER the

$ sed -n '1115p' docs/gallery-campaign-log/g2.md
literal body outside any short-circuit, PASS); then the two-flag          <- unrelated

$ grep -n "E3's boundary paragraph" docs/gallery-campaign-log/g2.md
1126: …                                                                   <- now :1126
```

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g2.md` |
| line | 1260 |
| old text | `` (`:1115`, §"THE BOUNDARY, probe-verified AFTER the build") `` |
| new text | `` (§"FLAGGED FOR RECORDS PASS 2", item 1) `` |
| derivation | the three commands above |
| output | as shown above |

### F-2c / F-2d — `trip-report:267` and `:304`, the cite `g2.md:1160-1173`

R2 proof, BOTH values:

```
$ git show 53a44689:docs/gallery-campaign-log/g2.md | sed -n '1160,1161p'
Read the conjunction. `fnHasRecv` was ALWAYS saved and restored across a
function literal (`savedFnRecv`, `emit.go:5339`), …

$ sed -n '1160,1161p' docs/gallery-campaign-log/g2.md
        }                                                                  <- mid code block
        …hoist…

$ grep -n "Read the conjunction\|So C1 was not only an over-refusal" docs/gallery-campaign-log/g2.md
1171: …   1179: …                                                          <- shifted +11
```

| field | value |
|---|---|
| file | `docs/2026-08-16_gallery-campaign-trip-report.md` |
| lines | 267 and 304 |
| old text | `` `g2.md:1160-1173` `` (both sites) |
| new text | `` `g2.md` §"THE E6 REGISTER WALK" `` (both sites) |
| derivation | the three commands above |
| output | as shown above |

---

## F-3 — the two remaining cross-doc cites

### F-3a — `g2.md:1263`, `docs/verified-examples.md:3500-3509`

R2 proof, BOTH values — the cite is not merely convention-noncompliant, it
is WRONG at tip (it now points into the entry's verbatim Go block):

```
$ git show 53a44689:docs/verified-examples.md | sed -n '3500,3502p'
**Why this example exists.** Idiomatic Go writes `isEven(a) && isEven(b)` —
a CALL in a short-circuit operand — and the frontend quarantined exactly
that, fail-closed, so this example was landed BLOCKED (nine red rows, …

$ sed -n '3500,3502p' docs/verified-examples.md
	}
	for {
		for isEven(b) {                        <- inside the verbatim Go block

$ grep -n '^## stein' docs/verified-examples.md
3467:## stein — binary GCD (Stein's algorithm), the extension-E3 consumer

$ grep -n 'Why this example exists' docs/verified-examples.md | sed -n '…'
3522:**Why this example exists.** …                <- the paragraph, today
```

(`verified-examples.md` went 4176 → 4198 lines between `53a44689` and tip.)

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g2.md` |
| line | 1263 |
| old text | `` (`docs/verified-examples.md:3500-3509`) `` |
| new text | `` (`docs/verified-examples.md` §`stein`, "**Why this example exists.**") `` + a bracketed note recording the old cite and that it was correct at `53a44689` |
| derivation | the four commands above |
| output | as shown above |

### F-3b — `wp-library-design.md` historical-cites header

Not a repoint: the header already declares the report's `g1.md:NNNN` cites
historical, and the body is left untouched by instruction. What is NOT
commit-qualified is the header's own MEASUREMENT, and that measurement is
now stale:

```
$ for c in 3aac907e 53a44689 3a6218cb; do echo "$c $(git show $c:docs/gallery-campaign-log/g1.md|wc -l)"; done
3aac907e 3862
53a44689 4075        <- 4075-3862 = +213, exactly the header's figure
3a6218cb 4127        <- 4127-3862 = +265 today
```

So `+213` was true at `53a44689` and is false at tip ⇒ qualify it with the
commit rather than re-measure a number that will drift again next round.

| field | value |
|---|---|
| file | `docs/2026-08-16_wp-library-design.md` |
| lines | 8-12 (PROVENANCE header) |
| old text | `and bucket B's edits shifted `g1.md`'s numbering (+213 lines)` |
| new text | `… (+213 lines as of `53a44689`; the drift keeps growing — the point is that the cites are historical, not what the current offset is)` |
| derivation | the loop above |
| output | as shown above |

---

## F-4 — `g1.md:4055`, the self-refuting grep sentence

R2 proof: the sentence asserts the grep "returns nothing", and running it
returns two hits — both of them the errata's own lines.

```
$ grep -rn '\b38\b' docs/gallery-campaign-log/g1.md docs/2026-08-16_gallery-campaign-trip-report.md docs/2026-08-16_wp-library-design.md
docs/gallery-campaign-log/g1.md:4048:   put the designated-headline count at **38**. **It is 56.** The
docs/gallery-campaign-log/g1.md:4055:   The 38 appears in no tracked file — `grep -rn '\b38\b'` over this log,
```

Writing the errata is what falsified the errata's own evidence sentence.

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g1.md` |
| lines | 4055-4057 |
| old text | `The 38 appears in no tracked file — `grep -rn '\b38\b'` over this log, the trip report and the WP-library note returns nothing — so nothing downstream inherited it` |
| new text | restated honestly: the grep now finds only this errata's own lines; at the time of the error the value appeared in the derivation record only, so nothing downstream inherited it |
| derivation | the grep above |
| output | as shown above |

---

## F-5 — `trip-report:337`, the "one per repair round" gloss

R2 proof, from the repairing commits the same bullet names:

```
$ git log --oneline -1 798a24af   -> Audit fix bucket A: gallery repairs (the splice, the counts, the false first)
$ git log --oneline -1 0ab348ce   -> Audit fix bucket B: log/summary reconciliation, ledger counts, dangling cites
$ git log --oneline -1 a816aa65   -> Fix round #2, item 1: THE THIRD SPLICE — three cost tables back to their units
```

Splices 1 and 2 were repaired by buckets A and B of the SAME round (the
2026-08-16 audit-fix round); only splice 3 belongs to a later round (fix
round #2). "One per repair round" is false.

| field | value |
|---|---|
| file | `docs/2026-08-16_gallery-campaign-trip-report.md` |
| line | 337 |
| old text | `There were **THREE** splices, not one, one per repair round:` |
| new text | gloss deleted and replaced by the true grouping (two in the audit-fix round, one in fix round #2), with the SHAs left in place |
| derivation | the three `git log` commands above |
| output | as shown above |

---

## F-6 — `g1.md:3465`, "all ten `.lean` line cites"

R2 proof, from round #3's own sweep record. `.tmp/fix3-manifest.md:112-131`
enumerates the sweep in two parts: a grep listing nine hits (ten cites —
`Sieve/Machine.lean` carries `:365` AND `:373` on one line), and then, in
prose, "**plus** the two live cites at `:3935`/`:3936`/`:3938`
(`DedupAdjacent.lean` :686, :2666; `SliceQueue.lean` :1561)" — THREE more
cites, all three of which appear in the manifest's own Verified-CORRECT
table (`.tmp/fix3-manifest.md:143-144`). So the sweep covered thirteen, and
the note undercounts its own work.

Those three live today at `g1.md:3949-3953` (the GAP-CONVERT entry):

```
$ sed -n '3949,3953p' docs/gallery-campaign-log/g1.md
   ONE USED, ONE LATENT.** `DedupAdjacent.lean` declares it at :686 and
   CALLS it at :2666; `SliceQueue.lean` declares the identical one-line
   `with_unfolding_all rfl` fact for `uint64(x)` of an integer value at
   :1561 and never uses it (…)
```

Arithmetic after the correction: 13 cites, 2 corrected (`Stein/Run`,
`Scan2`), 11 verified correct — so the trailing "other eight" moves to
"other eleven" in the same sentence or the note contradicts itself.

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g1.md` |
| lines | 3464-3470 |
| old text | `which swept all ten `.lean` line cites in this file` … `The other eight cites verified correct and were left alone.` |
| new text | `all thirteen` … `The other eleven verified correct`, plus the explicit statement that the three GAP-CONVERT cites below are among them |
| derivation | `.tmp/fix3-manifest.md:112-131,143-144`; the `sed` above |
| output | as shown above |

---

## ITEM 7 — the "zero hand-rolled `stepFn` unfoldings" half does NOT hold

R2 proof, BOTH values. The claim was made in the flagship's landing commit
`a82a04ba`; at that commit the tree contained exactly one such unfolding:

```
$ git show a82a04ba:proofs/GoLeanProofs/Examples/Histogram/Machine.lean | sed -n '322p'
  simp only [stepFn, hne, Bool.false_eq_true, if_false]

$ git show a82a04ba:proofs/GoLeanProofs/Examples/Histogram/Machine.lean | grep -n 'simp only \[stepFn'
322:  simp only [stepFn, hne, Bool.false_eq_true, if_false]      <- exactly one

$ git show a202b402:proofs/GoLeanProofs/Examples/Histogram/Machine.lean | grep -n 'simp only \[stepFn'
    (no output)                                                  <- removed here

$ git log --oneline -1 a202b402
a202b402 Kit-gap closure GAP-M1: the mapIterK choice-pick step -> MapMem

$ grep -n 'simp only \[stepFn' proofs/GoLeanProofs/Examples/Histogram/Machine.lean
    (no output)                                                  <- and still absent at tip
```

So "ZERO hand-rolled `simp only [stepFn, …]` unfoldings" was FALSE when
written and became true only later, at `a202b402`. The trip report's
"The second half holds;" is therefore wrong, and so is the twin in `g1.md`,
which states the claim without qualification.

### Edit 7a

| field | value |
|---|---|
| file | `docs/2026-08-16_gallery-campaign-trip-report.md` |
| line | 369 |
| old text | `The second half holds;` |
| new text | the second half is qualified: it did NOT hold when written (`Histogram/Machine.lean:322` carried one at `a82a04ba`); it holds only from `a202b402` on |
| derivation | the five commands above |
| output | as shown above |

### Edit 7b

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g1.md` |
| lines | 254-256 (inside the flagship's "What the kit DID carry") |
| old text | `**366 kit invocations across the five histogram modules, and ZERO hand-rolled `simp only [stepFn, …]` unfoldings** on either half of the work.` |
| new text | same sentence, with the ZERO half carrying the same qualification |
| derivation | the five commands above |
| output | as shown above |

---

## ITEM 8 — the pack-cite endpoints, stated so nobody re-litigates them

Round #3 declined to change `:113`/`:141` and recorded why in its manifest
(`.tmp/fix3-manifest.md:172-176`) — but not in the DOC, which is where the
next reader looks. Pass #4 raised it again, which is the evidence that the
reason has to live in the doc.

The convention, verified at tip:

```
$ sed -n '86p;113p;119p' proofs/GoLeanProofs/Examples/FibMemo/Rec.lean
def FreshFrom (h : Heap) (na : Nat) : Prop :=
theorem lookup_set_other {h : Heap} {a x : Nat} {c : HeapCell} (hne : a ≠ x) :
theorem lookup_set_self {h : Heap} {l : Loc} {c : HeapCell} :

$ sed -n '96p;141p;149p' proofs/GoLeanProofs/Examples/Stein/Run.lean
private def FreshFrom (h : Heap) (na : Nat) : Prop :=
private theorem lookup_set_other {h : Heap} {a x : Nat} {c : HeapCell}
private theorem lookup_set_self {h : Heap} {l : Loc} {c : HeapCell} :
```

Both ranges run `def FreshFrom` → `lookup_set_other`, self-consistently.
`lookup_set_self` sits at `:119` / `:149`, OUTSIDE both ranges — which is
exactly why the endpoints look wrong to a reader who expects the whole pack.

| field | value |
|---|---|
The "whole pack extent" figures carried over from round #3 were re-verified
this round rather than trusted:

```
$ awk 'NR>=84&&NR<=131&&/^ *(private )?(theorem|def)/{print NR": "$0}' proofs/GoLeanProofs/Examples/FibMemo/Rec.lean
86: def FreshFrom …   89: FreshFrom.mono   94: FreshFrom.push   103: FreshFrom.set
113: lookup_set_other  119: lookup_set_self
$ sed -n '129,130p' proofs/GoLeanProofs/Examples/FibMemo/Rec.lean
(blank) / `/-! ## The callee `Func`, verbatim, pinned -/`   -> pack ends :128 ✓

$ awk 'NR>=94&&NR<=178&&/^ *(private )?(theorem|def)/{print NR}' proofs/GoLeanProofs/Examples/Stein/Run.lean
96 99 103 111 123 133 141 149 161 168 172
$ sed -n '175,176p' proofs/GoLeanProofs/Examples/Stein/Run.lean
(blank) / `/-! ## The pinned callee `Func`s, transcribed`   -> pack ends :174 ✓
```

The clarification is written into the SAME bracketed note as F-6 (they sit
in one ledger entry), so the two are one edit in the file:

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g1.md` |
| lines | 3464-3470 (the bracketed sweep note; F-6 and item 8 land together) |
| old text | `The other eight cites verified correct and were left alone.]` |
| new text | + `**The `:113`/`:141` endpoints are not typos.**` … naming the `def FreshFrom` → `lookup_set_other` convention, `lookup_set_self` at `:119`/`:149` just past each range, and the `:128`/`:174` pack extents under the reading that makes them look wrong |
| derivation | the four commands above, plus the `sed -n '86p;113p;119p'` / `sed -n '96p;141p;149p'` pair |
| output | as shown above |

---

## THE CONVENTION — recorded in `INDEX.md`

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/INDEX.md` |
| line | after §"What the log is", the judgment-call format line |
| old text | (none — an addition) |
| new text | one line stating the R4 cite convention |
| derivation | user direction, fix round #4 |
| output | n/a |

---

## COMPLETE EDIT LIST (what the operator should find in the diff)

Six files, ten edits. Nothing else in the tree is touched. (The four
untracked `proofs_GoLeanProofs_Examples_Histogram_*.lean` files at the repo
root predate this round and are left exactly as found.)

| # | file | what |
|---|---|---|
| F-1a | `proofs/…/FibMemo/Rec.lean` | gateway attribution → 62/63, `Examples.Fib` exception, 20/42/1, six universal importers, no unique gateway; + `b5f0893c` errata line |
| F-1b | `docs/2026-08-16_wp-library-design.md` | the verbatim blockquote re-synced to F-1a |
| F-1b′ | `docs/2026-08-16_wp-library-design.md` | docstring-extent cite `:1359-1392` → `:1359-1404` (consequence of F-1a) |
| F-1c | `docs/2026-08-16_wp-library-design.md` | §"Designation-relevant input" attribution corrected |
| F-2a | `docs/gallery-campaign-log/g2.md` | `(:868)` → §-anchored |
| F-2b | `docs/gallery-campaign-log/g2.md` | `(:1115, …)` → §-anchored |
| F-2c/d | `docs/2026-08-16_gallery-campaign-trip-report.md` | `g2.md:1160-1173` ×2 → §"THE E6 REGISTER WALK" |
| F-3a | `docs/gallery-campaign-log/g2.md` | `verified-examples.md:3500-3509` → §`stein`, "**Why this example exists.**" |
| F-3b | `docs/2026-08-16_wp-library-design.md` | historical-cites header measurement commit-qualified `@ 53a44689` |
| F-4 | `docs/gallery-campaign-log/g1.md` | the self-refuting grep sentence restated honestly |
| F-5 | `docs/2026-08-16_gallery-campaign-trip-report.md` | "one per repair round" gloss corrected (2 in one round, 1 later) |
| F-6 + item 8 | `docs/gallery-campaign-log/g1.md` | "all ten" → "all thirteen", "other eight" → "other eleven", + the `:113`/`:141` endpoint convention stated |
| item 7a | `docs/2026-08-16_gallery-campaign-trip-report.md` | "The second half holds;" → the `a82a04ba`/`a202b402` qualification |
| item 7b | `docs/gallery-campaign-log/g1.md` | the twin claim gets the same qualification |
| convention | `docs/gallery-campaign-log/INDEX.md` | the R4 cite convention, one entry in §"What the log is" |

**Verbatim-quote check** (the wp-note declares its blockquote a verbatim copy
of the `unorm_idem` docstring, so F-1a and F-1b must not drift apart):

```
$ python3 - (diff docstring lines 1359-1404 against the blockquote)
MISMATCH only at the two leading lines the quote deliberately omits
("Idempotence of the uint64 normal form …" + its blank); from
"GAP-WITNESS" onward the two are IDENTICAL, all 44 lines.
```

**Derivation script is TRACKED this round.** `.tmp/fix4-closure.py` (and its
robustness variant `.tmp/fix4-closure-robust.py`) are committed with `-f`
alongside this manifest. Round #3's F-1 numbers were unreproducible because
its derivation lived in untracked scratch — which is F-4's entire subject —
so this round does not repeat the pattern for the one MATERIAL fix it makes.

---

## OUT-OF-SCOPE OBSERVATIONS (flagged, NOT fixed — R1)

1. `wp-library-design.md` §"LINE-CITES ARE HISTORICAL" in the OPERATOR
   CROSS-CORRECTION NOTE (not the header) still says `g1.md` "went from
   3,862 lines at `3aac907e` to 4,075 at the time of writing", and its three
   spot-checks ("`:2649-2654` → now an `rle` cost row" etc.) are "now"-claims
   measured at `53a44689`. `g1.md` is 4,127 at `3a6218cb` and longer after
   this round. The instruction scoped F-3b to the HEADER sentence and said
   "body untouched", so this is left alone. It is the same class as F-3b and
   wants the same `@ 53a44689` qualification in a future round.
2. `Rec.lean:1368` "29 modules, zero under `Iris.`" — see the F-1 section:
   28 repo modules + `Std.Data.ExtTreeMap`, so not provably wrong under a
   defensible reading. Left alone; recorded so it is not re-litigated.

---

## GATES

Run once, on the complete round-#4 tree state (all edits present):

```
$ scripts/ci
  ok   core build (warning-free)
  ok   proofs + Audit gate
  ok   surface purity (Iris-free imports, chain-closed)
  ok   statement-TCB closure (designated theorems proved outside the trusted closure)
  ok   eval tests (136 ok)
  ok   negative baseline diff (no regression)      [311 cases]
  ok   baseline diff FULL (1853/1853, no regression)
RESULT: PASS                                       (exit 0)

$ scripts/render-gallery
render-gallery: ok — 159 verbatim blocks match their sources   (exit 0)
```

`--diff` not run and not owed: this round changes documentation and one Lean
DOCSTRING only — no statement, proof, gate or runtime code — so the recorded
full baseline (1853/1853) is the standing evidence, exactly as in round #3.
Full logs: `.tmp/fix4-ci-1.log`, `.tmp/fix4-render-1.log`.
