# Fix round #3 — edit manifest

Every edit made in fix round #3, written as the edit is made. Pass #4 verifies
THIS FILE against the tree. An edit absent from this manifest is a defect.

Base tip: `53a44689` (branch `gallery-campaign`, tree clean at start).

Rules in force: (R1) nothing off the enumerated list is touched; (R2) no
cite/number/claim is corrected until the CURRENT text has been PROVEN wrong,
with the derivation run for BOTH old and new value; (R3) every edit is
recorded below with file | line | old | new | derivation | output.

---

## F1 — g1.md:3746-3753, RESTORE the MatMul cite

**R2 proof that the current text is WRONG.**

Current text claims the `MatMul.lean:709` cite "cannot be resolved in this
tree" and that the file "has never been longer in any commit".

Derivation, OLD value (what the round-2 text asserted):

```
$ git log --oneline --all -- '*Examples/MatMul.lean'
9f5a66c2 G1 lane A2: matmul WITHDRAWN to an honest gap — groundwork lands, the unverified headline does not
889b0b5c Guardrails wave 11/15: matrix multiply over fixed arrays — corpus, pin, stub
```

True only of the *tracked path history*. The withdrawn WIP was never on that
path — it lives on a snapshot ref, which `git log -- <path>` cannot see:

Derivation, NEW value:

```
$ git for-each-ref | grep -i bed0a4ea
bed0a4ead7153d3167cc60d699ded788ad6cd45c commit	refs/snapshots/gc-proofs-a/matmul-machine-layer

$ git show refs/snapshots/gc-proofs-a/matmul-machine-layer:MatMul.lean | wc -l
2375

$ git show refs/snapshots/gc-proofs-a/matmul-machine-layer:MatMul.lean | sed -n '709p'
  with_unfolding_all rfl

$ git show refs/snapshots/gc-proofs-a/matmul-machine-layer:MatMul.lean | sed -n '1,709p' | grep -n '^theorem' | tail -1
697:theorem sm2_IS00_raw (σ : ExecState) (sv sp sp2 x0 x1 x2 x3 x4 x5 x6 x7 x8 : Int)
```

So line 709 IS `with_unfolding_all rfl`, inside `sm2_IS00_raw`, in a 2,375-line
file that g1.md ITSELF cites 40 lines earlier (`g1.md:3705-3712`). The round-2
disclaimer is false. VERDICT: correct it.

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g1.md` |
| lines | 3745-3753 |
| old text | `` `MatMul.lean` — a cite that cannot be resolved in this tree, and says so rather than pointing somewhere wrong. [Re-pointed 2026-08-16, fix round #2: it read `MatMul.lean:709`, which resolves to nothing — the landed file is 336 lines (`git show 9f5a66c2:…/MatMul.lean | wc -l`) and has never been longer in any commit (`git log -- …/MatMul.lean` lists exactly two: 109 lines at `889b0b5c`, 336 at the withdrawal `9f5a66c2`). The 709-line module is the unlanded WIP this unit withdrew; the measurement stands, the file it was taken in does not exist here.]`` |
| new text | cite restored to `refs/snapshots/gc-proofs-a/matmul-machine-layer:MatMul.lean:709` (`with_unfolding_all rfl` in `sm2_IS00_raw`), with a one-line note recording the round-2 error |
| derivation | the four commands above |
| output | as shown above |

---

## F2 — trip-report:311-315, the three-splices list

**R2 proof that the current text is WRONG.** The list read: "the gallery's
dedup/palin split, `g1.md`'s sieve/stack cost-table swap, and a third: stack's
own Costs table ... off the end of the `wordfreq` unit". Items 2 and 3 there
are two MOVES INSIDE ONE COMMIT; the actual second splice is missing.

Derivation:

```
$ git log -1 --format=%B a816aa65 | head -12
Fix round #2, item 1: THE THIRD SPLICE — three cost tables back to their units
...
- sieve's table -> the G1.8 unit
- stack's table + the "Measured first-hand" / "CORRECTION" / "Honest
  standing" paragraphs -> the G1.7b unit
- the dangling copy deleted from wordfreq
```

=> the "sieve/stack swap" and the "dangling table off wordfreq" are moves 1
and 3 of `a816aa65`, i.e. ONE splice, listed twice.

```
$ git log -1 --format=%B 0ab348ce | grep -A4 'SECOND SPLICE'
- B4a THE SECOND SPLICE: palin's unit carried DotProduct's cost table and
  dotprod's worker narrative, while palin's own table and its two JC
  bullets sat orphaned in the lane-A process-finding section. Both blocks
  restored to their units, verbatim from their landing commits (b3534603,
  76efa5f3).
```

=> the real splice #2 (palin/dotprod, `g1.md`) was dropped from the list.
Splice #1 = `798a24af` A1 (dedup/palin, `verified-examples.md`). VERDICT:
correct it.

| field | value |
|---|---|
| file | `docs/2026-08-16_gallery-campaign-trip-report.md` |
| lines | 311-315 |
| old text | `There were **THREE** splices, not one — the gallery's dedup/palin split, `g1.md`'s sieve/stack cost-table swap, and a third: stack's own Costs table (with its 2540 MiB correction) left dangling, headingless, off the end of the `wordfreq` unit, while the `sieve` unit sat with zero table rows.` |
| new text | the three splices enumerated one per repair round, each with its repairing SHA: (1) dedup/palin `798a24af` A1, (2) palin/dotprod `0ab348ce` B4a, (3) sieve/stack/wordfreq `a816aa65`; plus a bracketed round-3 correction note |
| derivation | the two `git log -1 --format=%B` commands above |
| output | as shown above |

---

## F3 — g1.md, sweep of every `.lean` line cite

**Method.** Enumerated every line cite into a `.lean` file in `g1.md`:

```
$ grep -noE '[A-Za-z0-9_/.-]+\.lean`? ?\(?:[0-9]+(–[0-9]+|-[0-9]+)?' docs/gallery-campaign-log/g1.md
2900:proofs/GoLeanProofs/HeapBridge.lean:277
3452:FibMemo/Rec.lean` (:86–113
3452:Stein/Run.lean` (:99–141
3454:Sieve/Machine.lean` (:365          [+ `:373` on the same line]
3456:Histogram/HarnessR.lean` (:911
3456:WordFreq/Scan2.lean` (:1952
3459:Frame/Sim.lean:149
3746:MatMul.lean:709                    [F1]
3960:SliceStack.lean:1072
```

plus the two live cites at `:3935`/`:3936`/`:3938` (`DedupAdjacent.lean` :686,
:2666; `SliceQueue.lean` :1561). `g1.md:3949`'s `(:1579, :697)` is explicitly
labelled as the PREVIOUS, drifted pair — a historical record, not a live cite —
so it is not a sweep target.

**Verified CORRECT (left untouched), each by `sed -n '<N>p' <file>`:**

| cite | resolves to |
|---|---|
| `HeapBridge.lean:277` | `theorem intKind_normalize_idem (kind : IntKind) (v : Int) :` |
| `FibMemo/Rec.lean:86` | `def FreshFrom (h : Heap) (na : Nat) : Prop :=` |
| `FibMemo/Rec.lean:113` | `theorem lookup_set_other {h : Heap} {a x : Nat} ...` |
| `Sieve/Machine.lean:365` | `private theorem lookup_set_other {h : Heap} ...` |
| `Sieve/Machine.lean:373` | `private theorem lookup_set_self {h : Heap} ...` |
| `Sieve/Machine.lean` "docstring says `FreshFrom`-style" | `:37` — `Heap-algebra helpers (`FreshFrom`-style dead-region facts,`; `grep -n FreshFrom` returns ONLY `:37`, confirming "without the `FreshFrom` def" |
| `Histogram/HarnessR.lean:911` | `private theorem lookup_set_self {h : Heap} ...` (and it IS `private`) |
| `Frame/Sim.lean:149` | `theorem Heap.lookup_set_self {h : Heap} {k : Loc} ...` |
| `SliceStack.lean:1072` | `theorem pu_R1 (σ : ExecState) (ch : Choices) :` (first `pu_*` in the file) |
| `SliceQueue.lean:1561` | `theorem applyStrictOp_convert_u64 {σ : ExecState} {v : Int} {k : IntKind} :` |
| `DedupAdjacent.lean:686` / `:2666` | declaration / call site; `grep -n applyStrictOp_convert_u64` over the two files returns exactly those three hits, as the text says |

**F3a — `Stein/Run.lean` (:99–141) → (:96–141).** R2 proof:

```
$ sed -n '96p;99p' proofs/GoLeanProofs/Examples/Stein/Run.lean
private def FreshFrom (h : Heap) (na : Nat) : Prop :=
private theorem FreshFrom.mono {h : Heap} {na na' : Nat} (hle : na ≤ na')
```

Old start `:99` is `FreshFrom.mono`, not the def. The sentence calls these
"FULL `FreshFrom` packs" in explicit contrast with "the same dead-region
algebra WITHOUT the `FreshFrom` def" — so the range must include the def, and
FibMemo's parallel cite does start at its def (`:86`). Not drift: the same
lines read identically at `0ab348ce` where the cite was written
(`git show 0ab348ce:...Stein/Run.lean | sed -n '96p'` → same). WRONG when
written. VERDICT: correct to `:96`.

**Endpoints `113` / `141` NOT changed** — both resolve to the
`lookup_set_other` declaration in their own file, a self-consistent
convention. Under a "whole pack extent" reading they would both be wrong
(packs run to `:128` and `:174`), but the text states no convention and one
consistent reading makes them right. Not provably wrong ⇒ R2 leaves them.

**F3b — `WordFreq/Scan2.lean` (:1952) → (:1935).** R2 proof, BOTH values:

```
$ git show 0ab348ce:proofs/GoLeanProofs/Examples/WordFreq/Scan2.lean | sed -n '1952p'
theorem lookup_set_self (h : Heap) (l : Loc) (c : HeapCell) :      <- correct WHEN WRITTEN

$ sed -n '1952p' proofs/GoLeanProofs/Examples/WordFreq/Scan2.lean
    Heap.lookup (D ++ [(.base ⟨na⟩, c0), (.base ⟨na + 1⟩, c1),     <- now mid-body of lookup_c6of6

$ grep -n '^theorem lookup_set_self' proofs/GoLeanProofs/Examples/WordFreq/Scan2.lean
1935:theorem lookup_set_self (h : Heap) (l : Loc) (c : HeapCell) :
```

Drifted by 17 lines when bucket C (`007b6a97`) deleted dead declarations
above it. VERDICT: correct to `:1935`.

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g1.md` |
| line | 3452 |
| old text | `` `Stein/Run.lean` (:99–141) `` |
| new text | `` `Stein/Run.lean` (:96–141) `` |
| derivation | `sed -n '96p;99p' proofs/GoLeanProofs/Examples/Stein/Run.lean` |
| output | `private def FreshFrom …` / `private theorem FreshFrom.mono …` |

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g1.md` |
| line | 3456 |
| old text | `` `WordFreq/Scan2.lean` (:1952) `` |
| new text | `` `WordFreq/Scan2.lean` (:1935) `` + a bracketed note recording the sweep (ten cites), both corrections and their causes, and that the other eight verified correct |
| derivation | the three commands above |
| output | as shown above |

---

## F4 — g1.md, `Examples/SliceStack.lean` stub count 226 → 225

**R2 proof, BOTH values:**

```
$ git log -1 --format='%H %s' 9332cb70
9332cb70ac57ac6e4c4eb24f709cb2d80f10bd6e Guardrails wave 12/15: stack via slice — corpus, golden pin, stub root

$ git show 9332cb70:proofs/GoLeanProofs/Examples/SliceStack.lean | wc -l
225
```

`9332cb70` is the file's FIRST commit (`git log --oneline --all -- <path>`
lists 9332cb70, 6b5c226c, 0ab348ce, 007b6a97), i.e. the stub root. Old value
226 is not the count at that or any commit. VERDICT: correct to 225.

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g1.md` |
| line | 3301 |
| old text | `` | `Examples/SliceStack.lean` (stub 226 → full) | 6919 | 152.2 s | **2540 MiB** | `` |
| new text | `` | `Examples/SliceStack.lean` (stub 225 → full) | 6919 | 152.2 s | **2540 MiB** | `` |
| derivation | `git show 9332cb70:proofs/GoLeanProofs/Examples/SliceStack.lean \| wc -l` |
| output | `225` |

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g1.md` |
| line | after 3321 (new block) |
| old text | *(none — added)* |
| new text | `**Stub count corrected, fix round #3 (2026-08-16).**` paragraph recording 226 → 225 with the command and the commit's subject line |
| derivation | as above |
| output | `225` |

---

## F5 — g1.md, `Examples/SliceQueue.lean` "(5,297 → full)"

**R2 proof, BOTH values.** The file has exactly four commits; every one
measured:

```
$ git log --oneline --all -- proofs/GoLeanProofs/Examples/SliceQueue.lean
007b6a97 / 0ab348ce / 26bf2a90 / 1ba34153

$ for c in 1ba34153 26bf2a90 0ab348ce 007b6a97; do \
    git show $c:proofs/GoLeanProofs/Examples/SliceQueue.lean | wc -l; done
225      # 1ba34153 "Guardrails wave 13/15: queue via slice — corpus, golden pin, stub root"
8498     # 26bf2a90 the landing
8495     # 0ab348ce bucket B
8473     # 007b6a97 bucket C

$ wc -l < proofs/GoLeanProofs/Examples/SliceQueue.lean
8473
```

**5,297 is not among {225, 8498, 8495, 8473}** — it matches no commit of
this file. The stub is 225 (at `1ba34153`), exactly mirroring stack's stub.
The `8,498` in the `lines` column is CORRECT (landing state) and is left
alone. VERDICT: correct the label.

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g1.md` |
| line | 3984 (pre-edit numbering: 3966/3971) |
| old text | `` | `Examples/SliceQueue.lean` (5,297 → full) | 8,498 | **137.00 s** | **2313 MiB** | `` |
| new text | `` | `Examples/SliceQueue.lean` (stub 225 → full) | 8,498 | **137.00 s** | **2313 MiB** | `` |
| derivation | the `for c in …` loop above |
| output | `225 / 8498 / 8495 / 8473` |

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g1.md` |
| line | after 3998 (new block) |
| old text | *(none — added)* |
| new text | `**Stub label corrected, fix round #3 (2026-08-16).**` paragraph: 5,297 matches no commit, the four measured counts shown in a fenced block, honest label stated as "stub 225 → full 8,498 at landing (8,473 at the tip)", and an explicit refusal to guess where 5,297 came from |
| derivation | as above |
| output | as above |

---

## F8 — g1.md errata block gains the round-2 count correction

**Nature of the item.** This is an ADDITION, not a correction of tracked
text: the wrong number (38) lived in fix round #2's untracked working
notes. R2's "prove the old text wrong" therefore applies to the NEW claim
being asserted — that the designated list is 56 — and to the assertion that
nothing tracked inherited the 38.

```
$ sed -n '/let designated : List Name := \[/,/^  \]/p' proofs/Audit.lean | grep -c '^ *``GoLean\.'
56

$ git log -1 --format=%s e4202039
Designate the verified-examples gallery headlines (48 -> 56)

$ git log -1 --format=%s 8101b726
Comparator landmark for the 48 -> 56 designation: PASS, 56/56 in 308 s

$ grep -rn '\b38\b' docs/gallery-campaign-log/ docs/2026-08-16_gallery-campaign-trip-report.md docs/2026-08-16_wp-library-design.md
(no output)
```

`proofs/Audit.lean`'s `designated` list is the one `scripts/comparator-judge`
parses (`scripts/comparator-judge:129`). Count = 56, corroborated by both
designation commits. No tracked file carries the 38.

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g1.md` |
| line | 4022 (heading) |
| old text | `### ERRATA — two claims that are wrong in a COMMIT MESSAGE and cannot be fixed there` + its lead-in paragraph ("Both errors are the same false claim, propagated:") |
| new text | `### ERRATA — claims that are wrong in a record this log cannot edit`, lead-in restated to scope items 1-2 to commit messages and item 3 to untracked working notes |
| derivation | required by the addition below — the old heading said "two" |
| output | n/a (structural) |

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g1.md` |
| line | after 4043 (new item 3) |
| old text | *(none — added)* |
| new text | errata item 3: round #2's derivation record said 38, the designated list is 56, with the `sed … \| grep -c` command, both designation commits, the `grep -rn '\b38\b'` null result showing nothing tracked inherited it, and the note that round #2 kept no manifest — which is why round #3 writes `.tmp/fix3-manifest.md` |
| derivation | the four commands above |
| output | `56` / the two subjects / no output |

---

## NIT (g1.md) — the nine wrapped `## ` heading lines, un-wrapped

**Problem (verified, not assumed).** Six unit headings were hard-wrapped
across multiple lines with `## ` repeated on every continuation, so each
continuation rendered as its own spurious H2:

```
$ awk '/^## /{if(prev==NR-1) print NR; prev=NR}' docs/gallery-campaign-log/g1.md
607 608 1530 1531 1781 2016 2280 2442 2443     (9 lines)
```

Nine continuation lines across six headings (606-608, 1529-1531, 1780-1781,
2015-2016, 2279-2280, 2441-2443). Joined each group into one `## ` line,
stripping the `## ` prefix from continuations only — no wording changed.

| field | value |
|---|---|
| file | `docs/gallery-campaign-log/g1.md` |
| lines | 606-608, 1529-1531, 1780-1781, 2015-2016, 2279-2280, 2441-2443 |
| old text | six headings split over 15 lines, 9 of them spurious `## ` continuations |
| new text | the same six headings, one line each, wording byte-identical after joining on a single space |
| derivation | `grep -c '^## '` before vs after |
| output | before **37**, after **28** — exactly the 9 spurious H2s gone; `awk` re-run finds no remaining consecutive `## ` pair |
| gates | `scripts/render-gallery` → `ok — 159 verbatim blocks match their sources`, exit 0; `scripts/ci` → **RESULT: PASS** (1853/1853, no regression) |

---

## NIT (g1.md:2152) — "fourth" → "fifth": **REFUSED under R2**

The current text is **RIGHT**; I could not prove it wrong, and the evidence
runs the other way. Both values derived:

The sentence: *"InsertionSort carries it THREE times (`ρsh` at threshold 4,
`ρ11` at 11, `ρ21` at 21 …); SelectionSort now carries **a fourth** (`ρ16` at
threshold 16 …)"*.

The ledger this must agree with is bucket B's B12 correction, which fixed the
frame/rebase layer at **FIVE sites**, enumerated in order:
`rho_sh 4, rho11 11, rho21 21, selsort 16, bubble 16`. On that enumeration
selsort's `ρ16` is site **four** and bubble's is site five.

Confirmed against the tree, not the note:

```
$ grep -rhoE '(rebaseSim|shiftSpec|frameSim)[A-Za-z0-9_]*' proofs/GoLeanProofs/Examples/InsertionSort/*.lean | sort -u
frameSim_zero  frameSim_zero11  frameSim_zero21
rebaseSim      rebaseSim11      rebaseSim21      shiftSpec_
```

=> InsertionSort carries exactly THREE rebase families (thresholds 4, 11, 21),
as the sentence says. SelectionSort's is therefore the fourth.

```
$ grep -rn 'GAP-WITNESS' proofs/GoLeanProofs/Examples/*/Frame.lean
proofs/GoLeanProofs/Examples/BubbleSort/Frame.lean:14
proofs/GoLeanProofs/Examples/SelectionSort/Frame.lean:34
proofs/GoLeanProofs/Examples/SelectionSort/Frame.lean:70
```

selsort and bubble both landed in ONE commit (`a0549b91`, "[lane B] twosum +
selsort + bubble"), so no landing order separates them either; the log's own
order puts the selsort unit (`:2010`) before the bubble unit (`:2273`).

**VERDICT: refused.** "a fourth" at `:2152` is correct. NOT CHANGED.

*Adjacent observation, deliberately NOT acted on (R1: not on the list).* If
anything near here is off it is `:2144`, "the third-and-fourth landed
copies" — under the same site enumeration the copies selsort and bubble add
are the fourth and fifth. That line was not on the enumerated list, so it is
left untouched and reported instead.

---

## F6 — the FibMemo `unorm_idem` ruling comment, restated on its true basis

**R2 proof that the current text is WRONG.** The comment argued: *"and no
module under `Examples/` imports Iris"*. Measured over the tree by building
the transitive import closure of every module under `proofs/GoLeanProofs/Examples/`
(script: `.tmp/irisdep.py`, `.tmp/irispath.py` — module `A.B` resolved to
`./A/B.lean` or `proofs/A/B.lean`, imports read from the file's `import` lines):

```
Examples modules: 132
transitively import Iris: 63
Iris-free: 69

gateway (module in closure that DIRECTLY imports Iris):
  GoLeanProofs.Ghost                             62
  GoLeanProofs.Adequacy                          1

shortest path, sample:
  GLP.Examples.ArrayPalindrome.Machine -> GLP.Laws.StmtOps -> Iris.ProgramLogic.WeakestPre

second hop histogram (the example's own direct import that leads to Iris):
  GoLeanProofs.Laws.StmtOps                  20      (+43 reaching it via a sibling)
```

corroborated at the gateway itself:

```
$ grep -n '^import' proofs/GoLeanProofs/Laws/StmtOps.lean | head -5
1:import Iris.ProgramLogic.WeakestPre
2:import Iris.ProgramLogic.Lifting
3:import Iris.ProgramLogic.Adequacy
4:import Iris.ProofMode
5:import Iris.BI.Lib.GenHeap
```

**63 of 132 — the claim was false.** The TRUE fact, which is what the ruling
actually rests on, verified separately:

```
FibMemo.Rec transitively imports Iris? False
FibMemo.Rec closure size: 29
Iris modules in closure: []
```

VERDICT: the ruling STANDS, its stated basis does not. Restate on the
direct/module-local basis.

| field | value |
|---|---|
| file | `proofs/GoLeanProofs/Examples/FibMemo/Rec.lean` |
| lines | 1365-1372 (docstring of `theorem unorm_idem`) |
| old text | `What it does NOT have is a home an example module can import: … and no module under `Examples/` imports Iris — Iris is a proof device, not an example-layer dependency … it would have made this the first example module in the tree to import the Iris layer, to save four lines.` |
| new text | basis restated to "a home THIS module can import": **this file and its whole transitive closure are Iris-free (29 modules, zero under `Iris.`)**, keeping them so preserves the FOOTPRINT layer's independence; consequence reworded to "would have put the Iris layer into a closure that does not otherwise contain it". Plus an **NB** paragraph recording that the old tree-wide claim was FALSE, with the 63/132 measurement, the `Laws.StmtOps` gateway and the 20-direct/43-transitive split, and the explicit statement that the ruling now stands on the module-local basis and never on a tree-wide property |
| derivation | `.tmp/irisdep.py`, `.tmp/irispath.py`, `grep -n '^import' proofs/GoLeanProofs/Laws/StmtOps.lean` |
| output | as shown above |

| field | value |
|---|---|
| file | `docs/2026-08-16_wp-library-design.md` |
| lines | 228-254 (§(a), the blockquote of that ruling) |
| old text | cite `Rec.lean:1359-1378` + the blockquote carrying the old "no module under `Examples/` imports Iris" wording |
| new text | cite updated to `Rec.lean:1359-1392` (docstring grew: `grep -n` → opens 1359, closes 1392); blockquote re-synced to the new docstring including the NB paragraph; **plus one added paragraph** "Designation-relevant input (recorded 2026-08-16, fix round #3)" flagging the 63/132 measurement as an input to designation — "keep Iris out of `Examples/`" is not an available policy, so Iris-freedom is a per-module property to state and check, not to assume from a directory |
| derivation | `grep -n 'Idempotence of the uint64\|not audit-round work. -/' proofs/GoLeanProofs/Examples/FibMemo/Rec.lean` |
| output | `1359:` … `1392:` |

---

## NIT — the wp-note's seven self-cites, +6 offset

**R2 proof.** The whole file IS reviewer 5's report (title at `:30`) with an
operator cross-correction note appended at `:196`. Seven cites point into its
own body and were written against R5's STANDALONE report, never rebased on
landing. Each verified by CONTENT (not by applying an offset), old and new:

| cite | old line resolves to | correct line | why |
|---|---|---|---|
| `:45` | P-A's Coverage line (`derive_entry_eq`) | **`:51`** | the P-B line that lists kadane in the `seed+i` affine bucket AND under "signed/Int-seeded" |
| `:148` | *(blank line)* | **`:154`** | item 4, `familyF/…/affine`, whose consumer list repeats kadane |
| `:55` (×2) | P-C prose, "The loop leaves either at its test…" | **`:62`** | the P-D Instances line — the ONLY line that both says "5 full hand instantiations" and carries `SelectionSort/Frame.lean:44,274,499` + `BubbleSort/Frame.lean:30,262,486`, the two cites the grading paragraph is about |
| `:145` | `---` (a rule) | **`:151`** | priority item 1, "— 5 (isort ×3, selsort, bubble…)" |
| `:26` | "addendum records this audit)…" | **`:32`** | the Basis line: "`FreshFrom` has **5** program-local copies" |
| `:62` | P-D Instances (a different claim) | **`:68`** | P-E Instances: "5 program-local copies — fibmemo…" |
| `:147` | `## 3. PARALLEL CONSTRUCTIONS…` (a heading) | **`:153`** | item 3, "The footprint pack … — 5 copies (fibmemo, stein, sieve…" |

Six are +6; `:55` is **+7** — so the offset was NOT applied blindly, each was
resolved against what the sentence claims the line says.

**NOT changed:** `:25` and `:36` in §(e) are not self-cites — they point into
`proofs/Audit/Kit.lean`. Verified: `sed -n '25p;36p' proofs/Audit/Kit.lean`
returns two English prose lines, and the three counts the paragraph turns on
re-derive exactly (`grep -c '^#guard_msgs in #print axioms '` → 116,
`grep -c '#print axioms'` → 118, `grep -c '#guard_msgs'` → 117).

| field | value |
|---|---|
| file | `docs/2026-08-16_wp-library-design.md` |
| lines | 282, 283, 314, 321, 342 |
| old text | `(`:45`)` / `` `:148` `` / `(`:55`, `:145`)` / `(`:55` cites` / `(`:26`, `:62`, `:147`)` |
| new text | `(`:51`)` / `` `:154` `` / `(`:62`, `:151`)` / `(`:62` cites` / `(`:32`, `:68`, `:153`)` |
| derivation | `sed -n '<N>p' docs/2026-08-16_wp-library-design.md` for each old and new line |
| output | the table above |

| field | value |
|---|---|
| file | `docs/2026-08-16_wp-library-design.md` |
| line | after 324 (new bracketed note) |
| old text | *(none — added)* |
| new text | bracketed note recording all seven re-pointings, that they were derived by content rather than by offset, the six-at-+6/one-at-+7 split, and that `:25`/`:36` are Kit.lean cites deliberately left alone |
| derivation | as above |
| output | as above |

---

## F7 — g2.md, the BOUNDARY UPDATE block's placement

**R2 proof.** Text said the block sits "above the E3 fidelity argument".

```
$ grep -n 'BOUNDARY UPDATE' docs/gallery-campaign-log/g2.md
518:**BOUNDARY UPDATE — the post-C1 world (2026-08-16, fix round #2; …

$ grep -n 'E3 — THE FIDELITY ARGUMENT' docs/gallery-campaign-log/g2.md
328:### E3 — THE FIDELITY ARGUMENT (2026-08-15, unit G2.E3 …)

$ grep -n 'THE BOUNDARY, probe-verified' docs/gallery-campaign-log/g2.md
504:**THE BOUNDARY, probe-verified AFTER the build (fail-closed
```

518 > 328: the block is 190 lines BELOW that heading, not above. It sits
immediately after E3's boundary paragraph (`:504`-`:516`) — which is the
paragraph open item 1 actually names (`:1115`, §"THE BOUNDARY,
probe-verified AFTER the build"). VERDICT: correct.

| file | `docs/gallery-campaign-log/g2.md` | line 1243-1245 |
|---|---|---|
| old text | `Item 1: the *BOUNDARY UPDATE* block above the E3 fidelity argument now states the post-C1 boundary precisely.` |
| new text | `the *BOUNDARY UPDATE* block (`:518`), attached directly to E3's boundary paragraph (`:504`, itself below the E3 fidelity argument at `:328`)` + bracketed correction note |
| derivation | the three greps above | output as shown |

---

## F12 — g2.md:977, the FOURTH "dot refusal" site

**R2 proof.** g2.md's own boundary probe, 109 lines above:

```
$ sed -n '868p' docs/gallery-campaign-log/g2.md
import . "strings"     "stuck": "GoCore function not found: Fields"   (the pre-existing dot-import gap, recorded in the findings — E5 neither widens nor narrows it)
```

`stuck`, not a refusal. The audit fixed this claim at three sites
(`INDEX.md:62-67`, and two others); the E5 status table's evidence cell was
the fourth and was missed. VERDICT: correct it in the same shape.

| file | `docs/gallery-campaign-log/g2.md` | line 977 (table cell) |
|---|---|---|
| old text | `Repeat/Sprint/value/dot refusals byte-identical` |
| new text | `Repeat/Sprint/value-position refusals byte-identical — and the dot-import case NOT a refusal: it emits a dangling call and the machine answers `stuck`, the pre-existing fail-closed defect E5 neither widened nor narrowed (`:868`) [corrected …, the fourth site of the claim the audit fixed at three]` |
| derivation | `sed -n '868p'` above; wording matched to `INDEX.md:62-67` | output as shown |

---

## F9 — verified-examples.md, the twosum row descriptors

**R2 proof: the Go ORACLE, not arithmetic by hand.** Every named row
recomputed from its own `cases.tsv` args by re-running the corpus's own
`twoSum` (probe: `.tmp/twosumprobe/main.go`, `GOCACHE` repo-local):

```
four-mid         -> (1,2)
four-first       -> (0,1)
four-last        -> (2,3)
four-notfound    -> (4,4)
four-same        -> (0,1)
four-dups        -> (0,2)
four-extremes    -> (0,1)
harness-r-empty  n=0 -> (0,0)  SENTINEL (no pair)
harness-r-one    n=1 -> (1,1)  SENTINEL (no pair)
harness-r-five   n=5 -> (3,4)  HIT s[3]+s[4] = 13+14
harness-r-eight  n=8 -> (0,7)  HIT s[0]+s[7] = 1+8
harness-r-wrap   n=8 -> (0,2)  HIT s[0]+s[2] = 9223372036854775807+9223372036854775809
```

**Three descriptors WRONG:**
- `n = 5` "(interior hit)" — it is `(3,4)`, the LAST TWO of five.
- `n = 8` "(adjacent hit at the head)" — it is `(0,7)`, first and last,
  the least adjacent pair available.
- the wrap row "the no-pair sentinel is what real Go returns" — real Go
  returns `(0,2)`, a HIT; `(2^63−1)+(2^63+1) = 2^64 ≡ 0`.

**Descriptors VERIFIED CORRECT and left alone** (R2): the six four-element
descriptors map exactly onto `four-mid/first/last/notfound/dups/same`
(middle/first/last/absent/duplicate/degenerate-duplicate); "an
`int64`-boundary extreme" = `four-extremes`; "the one-element and empty
drivers" = `one-notfound`, `empty`; "14 corpus rows" = the 14 data rows in
`cases.tsv`; and "no corpus row exercises a seed or target above 2^63 − 1"
holds (max over all args = 9223372036854775807).

| file | `docs/verified-examples.md` | lines 2587-2592 |
|---|---|---|
| old text | `… `n = 5` (interior hit), `n = 8` (adjacent hit at the head) and the wrap-region seed `9223372036854775807` with target `0`.` |
| new text | each row spelled with its args and its ACTUAL result — `n = 5` seed 10 target 27 hits `(3,4)` the final adjacent pair; `n = 8` seed 1 target 9 hits `(0,7)` the widest pair; the wrap row hits `(0,2)` with the `2^64 ≡ 0` arithmetic shown — plus a bracketed note naming all three old descriptors |
| derivation | the Go probe above | output as shown |

| file | `docs/verified-examples.md` | lines 2598-2599 |
|---|---|---|
| old text | `where the pair sums `≈ 2^64` DO wrap and the no-pair sentinel is what real Go returns).` |
| new text | wrap restated as LOAD-BEARING: the row's hit at `(0,2)` exists only because the sum wraps, so it is a positive test of wrapped addition rather than a boundary degrading to the sentinel |
| derivation | same probe | output: `harness-r-wrap n=8 -> (0,2) HIT` |

---

## NIT — twosum + rle gain the standard NOT-DESIGNATED clause

**Verified first (R2 applied to the new claim).** Both are genuinely not
designated:

```
$ grep -c '<name>' proofs/GoLeanProofs/Examples/Targets.lean        -> 0 for all of
   twosum_ok, twosum_readout, twosum_first_pair, rle_ok, rle_readout, rle_decode
$ sed -n '/let designated : List Name := \[/,/^  \]/p' proofs/Audit.lean | grep -i 'twosum\|rle'
   -> only a COMMENT listing audit SHARDS ("… TwoSum, SelectionSort, …", Audit.lean:1852),
      no designated entry
```

twosum's clause was bespoke prose and rle's was a two-clause abbreviation
("Not designated; absent from `Targets.lean` and the Comparator trusted
closure"). Both replaced with the standard opener used by the other 14
entries, keeping every entry-specific sentence that followed.

| file | `docs/verified-examples.md` | twosum `**Status.**`, rle `**Status.**` |
|---|---|---|
| old text | twosum: `This entry is NOT designated: it is absent from …`; rle: `Not designated; absent from `Targets.lean` and the Comparator trusted closure.` |
| new text | both now open `NOT DESIGNATED — see the note in *How to read an entry*: this example post-dates the 2026-08-14 designation, and designation is arc-end work under user sign-off, so its statement is not walked by the mechanized statement-TCB gate and not replayed by the Comparator judge.` followed by the four-surface absence list; rle's completed prose keeps its readout/corollary and deletion-test sentences |
| derivation | the greps above; `scripts/render-gallery` re-run |
| output | `render-gallery: ok — 159 verbatim blocks match their sources`, exit 0 (the per-section one-Status/one-Ground/one-Fuel count still passes) |

---

## F11 — trip report, C1 is TWO-directional

**R2 proof.** `g2.md:1160-1173`:

```
:1162  `hoistForbidden` was NOT — that is the C1 bug.
:1164  gate could not fire at all.** The `len` emitted inline, with no
:1168  **So C1 was not only an over-refusal.** …
:1171  nesting a function literal in a short-circuit RHS was a way
:1172  to walk around a fail-closed guard**, taking the inline lowering that E6
:1173  exists to refuse. That direction was not identified when the fix landed.
```

So `:262`'s "no gate was found failing open" is false as a statement about
the tree (true only of the audit's own findings), and the C1 paragraph
described one direction of a two-directional defect.

| file | `docs/2026-08-16_gallery-campaign-trip-report.md` | line 262 |
|---|---|---|
| old text | `no headline statement was wrong, no axiom pin moved, no gate was found failing open, and the differential's failing set …` |
| new text | the fail-open clause removed from the list and replaced by an explicit **"One gate WAS failing open, and the audit did not find it"** — E6, disabled by the same C1 defect, surfaced only in `b4179573`'s register walk — plus a bracketed note that the old phrasing was true of the audit and false of the tree |
| derivation | `sed -n '1160,1173p' docs/gallery-campaign-log/g2.md` | output as shown |

| file | `docs/2026-08-16_gallery-campaign-trip-report.md` | after line 284 |
|---|---|---|
| old text | *(none — added)* |
| new text | a second paragraph on the C1 defect: the `make`/`append` direction over-refused (fail-closed), while the E6 conjunct direction under-refused (fail-open) — same missing save/restore, opposite directions — with the `b4179573` provenance and the "walk every READER of that flag, in both directions" lesson |
| derivation | same | output as shown |

---

## F17 — the "366" claim, qualified at both surviving sites

**R2 proof: I could not reproduce 366 under any rule, at either commit.**
Over the five histogram modules:

| counting rule | at tip | at `a82a04ba` (flagship landing) |
|---|---|---|
| kit-family token occurrences | 258 | 318 |
| `stepFn*` tokens | 232 | 286 |
| `have` lines | 165 | 226 |
| qualified `StepKit./MapMem./…` refs | 18 | — |
| `exact`/`apply`/`refine` lines | 49 | — |

None is 366; the closest (318) is not a plausible miscount of a stated
rule. The trip report already names this among the campaign's false
claims; the two sites that still asserted it did not say so.

| file | `docs/gallery-campaign-log/INDEX.md` | line 237 |
|---|---|---|
| old text | `the kit carried every machine step (366 invocations, zero hand-rolled `stepFn` unfoldings).` |
| new text | `366 invocations — **UNREPRODUCIBLE: see the trip report's addendum**; … never been re-derived … at this tip or at the flagship's own landing commit `a82a04ba`, and it should not be repeated as measured` |
| derivation | the counting table above | output as shown |

| file | `docs/gallery-campaign-log/g1.md` | line 254 |
|---|---|---|
| old text | `— **366 kit invocations across the five histogram modules, and ZERO hand-rolled `simp only [stepFn, …]` unfoldings** on either half of the work.` |
| new text | claim left in place, followed by a bracketed **"The 366 is UNREPRODUCIBLE"** qualification carrying all five counting rules and both commits, and the instruction to treat it as an unverified figure |
| derivation | same | output as shown |

---

## F16 — INDEX date labels (four sites)

**R2 proof, BOTH values.** Each checkpoint's landing commit re-derived by
`git log -S"checkpoint <n> (unit" -- docs/gallery-campaign-log/INDEX.md | tail -1`:

```
charter      eda81a05  2026-08-14 21:16
ea7c689a               2026-08-14 21:52
checkpoint 1 aa455e07  2026-08-14 22:40
checkpoint 2 a82a04ba  2026-08-14 23:49
```

All four labels read 2026-08-15; all four events are 2026-08-14.

| file | `docs/gallery-campaign-log/INDEX.md` | lines 1, 7, 219, 243 |
|---|---|---|
| old text | `INDEX (2026-08-15 … 2026-08-16)` / `user-authorized 2026-08-15` / `- 2026-08-15, checkpoint 2` / `- 2026-08-15, checkpoint 1` |
| new text | `2026-08-14 … 2026-08-16` / `user-authorized 2026-08-14` / `- 2026-08-14, checkpoint 2` / `- 2026-08-14, checkpoint 1`, plus one bracketed note carrying all four derivations |
| derivation | the four `git log` lookups above |
| output | as shown |

**NOT changed:** `INDEX:3`'s `docs/2026-08-15_gallery-campaign.md` is a
FILENAME (the file exists under that name), not a date claim; renaming it
would break every cite. Recorded in the note.

---

## F13 — INDEX, "two id renames landed"

**R2 proof, from the commit itself:**

```
$ git log -1 --format='%B' 8b20dd37 | grep -A10 -i 'THE CHARTERED RENAME'
THE CHARTERED RENAME DID NOT LAND — operator ruling needed.
examples/reverse/harness-wrapping -> harness-near-max … was made, ran green,
and was then refused by scripts/ci's baseline re-pin guard … so the rename
was BACKED OUT …

Re-pin: 1791 cases, 1663 PASS, 128 FAIL … Drift is EXACTLY the 15 new ids
```

Wrong twice: no rename landed, and ONE was chartered, not two. "Drift is
EXACTLY the 15 new ids" independently excludes a landed rename. The
back-out is recorded twelve lines below in the same checkpoint.

| file | `docs/gallery-campaign-log/INDEX.md` | line 139 |
|---|---|---|
| old text | `` `tools/coverageharness` + two id renames + the re-pin, one commit `` |
| new text | `` `tools/coverageharness` + the re-pin, one commit `` + bracketed correction quoting `8b20dd37` |
| derivation | the `git log` above | output as shown |

---

## F14 — INDEX, "23 guardrail rows committed RED"

**R2 proof.** `191e7147` ("G2.E5 guardrails: … 23 rows RED first"):

```
- examples/wordfreq: … + 15 rows; 14 RED at frontend-export with the
  standing quarantine verbatim, build-text (setup only) PASSES as the control.
- strings/fields-conformance: 8 rows
- baselines/native-full.tsv re-pinned: EXACTLY 23 NEW ids
```

14 RED + 8 RED = **22 RED**; +1 PASSING control = **23 new ids**. The
downstream flip count corroborates: `g2.md`'s E5 row reads "22 rows RED
before / 22 flips after". VERDICT: the line double-counted the control.

| file | `docs/gallery-campaign-log/INDEX.md` | line 55 |
|---|---|---|
| old text | `then 23 guardrail rows committed RED with their own full-gate re-pin (14 wordfreq + 8 fields-conformance …)` |
| new text | `then **22 guardrail rows committed RED plus 1 PASSING control — 23 new ids** …` with the control named (`build-text`, setup-only) and a bracketed correction quoting `191e7147` |
| derivation | `git log -1 --format='%B' 191e7147` | output as shown |

---

## F15 — INDEX, "example modules net −131"

**R2 proof, every scope measured:**

```
$ git show --numstat --format='' 065da117
  (12 files under Examples/, plus EntryEq.lean +55/-14, plus g0.md +39/-0)

  Examples/ :  +129 -240  net -111
  proofs/   :  +184 -254  net  -70
  ALL files :  +223 -254  net  -31
```

−131 matches no scope. The line's own stated scope is "example modules"
⇒ **−111**.

| file | `docs/gallery-campaign-log/INDEX.md` | line 249 |
|---|---|---|
| old text | `example modules net −131` |
| new text | `**example modules net −111**` + bracketed note giving all three scopes (−111 Examples/, −70 proofs/, −31 all files) and the command |
| derivation | `git show --numstat --format='' 065da117` | output as shown |

---

## F10 — INDEX, post-checkpoint commit enumeration extended

**Derivation.** `git log --oneline --reverse 8cc7b39c..HEAD` gives the full
list; runtime-touching commits identified by file scope:

```
b070c10b 3aac907e                                   doc-only
798a24af 0ab348ce 9ee5f1f3 89a02d47 007b6a97
f2c6f756 d813f676 fa240552 9d131a4f                 audit fix round, buckets A-G
a816aa65 69c3b399 72757752 b4179573 dae9055c 53a44689   fix round #2
f75c92bb b5f0893c …                                 fix round #3

$ git show --stat --format='' b4179573 | tail -5
 .../exec/bools/short-circuit-funclit/cases.tsv | 12 ++
 .../exec/bools/short-circuit-funclit/main.go   | 166 +++
 baselines/native-full.tsv                      | 96 +-
 docs/gallery-campaign-log/g2.md                | 163 +++
```

=> `b4179573` is a CORPUS + re-pin commit; it touches no frontend, GoCore
or decoder code. Its record:

```
$ git log -1 --format='%B' b4179573 | grep -A2 'RE-PIN'
RE-PIN, same commit: baselines/native-full.tsv 1841 -> 1853 cases,
1743 -> 1753 PASS, 98 -> 100 FAIL. Drift is EXACTLY the twelve new ids;
```

| file | `docs/gallery-campaign-log/INDEX.md` | lines 263-271 |
|---|---|---|
| old text | prose naming `b070c10b`, `3aac907e` and "the post-autonomy audit fix round", with "One of those fix commits touches runtime code" |
| new text | a four-item numbered enumeration through fix round #3, naming every SHA, marking `9ee5f1f3`/`89a02d47` as the runtime pair and `b4179573` as a corpus+re-pin commit that touches no runtime code, and stating **the superseding record for clause 5 at the branch tip: `b4179573`'s 1853 / 1753 / 100** |
| derivation | the commands above | output as shown |

---

## NIT — checkpoint-7 SHA list

**R2 proof.** The list claims to be the tips of the EARLIER checkpoints.
Each tip re-derived:

```
checkpoint 1 aa455e07 | checkpoint 2 a82a04ba | checkpoint 3 a202b402
checkpoint 4 5897c02b | checkpoint 5 8b20dd37
```

Old list: `8b20dd37`, `5897c02b`, `b022de4e`, `300e3aa7`, `a82a04ba`.
`b022de4e` is the guardrails wave's last row commit and `300e3aa7` a
kit-gap-closure commit — neither is a checkpoint tip — and cp3/cp1's tips
were absent. The FINDING is unaffected, re-verified on the corrected list:

```
G4 shas {34f45448,51e1003b,feda430e,5275c914} ancestor of
  aa455e07 / a82a04ba / a202b402 / 5897c02b / 8b20dd37  -> no, all 20 checks
  46c04c0c (checkpoint 7)                               -> YES, all 4
```

| file | `docs/gallery-campaign-log/INDEX.md` | line 109 |
|---|---|---|
| old text | `` non-zero at `8b20dd37`, `5897c02b`, `b022de4e`, `300e3aa7`, `a82a04ba` `` |
| new text | `` non-zero at every earlier checkpoint tip: `8b20dd37` cp5, `5897c02b` cp4, `a202b402` cp3, `a82a04ba` cp2, `aa455e07` cp1 `` + a bracketed note that only the citation was wrong, not the finding |
| derivation | the checkpoint lookups + the 24 `git merge-base --is-ancestor` checks | output as shown |

---

## NIT — b4179573's "two readers"

**R2 proof.** `g2.md` said "C1's nine, plus the two readers C1 missed
(`splatMultiCall` and the elided `&composite` arm)". Those are two probed
SHAPES. The flag's actual readers:

```
$ grep -c 'if e\.hoistForbidden != ""' tools/nativefrontend/emit.go
13      (:1570 :1595 :4604 :4852 :4921 :5080 :5134 :5585 :6375 :6955 :7020 :7050 :7208)

$ sed -n '6355p' tools/nativefrontend/emit.go
		if e.fnHasRecv && e.hoistForbidden == "" {
```

13 + 1 = **14 guard sites**, the fourteenth being the E6 conjunct at the
OPPOSITE polarity — precisely the reader the register walk found failing
open. Eleven shapes, fourteen readers.

| file | `docs/gallery-campaign-log/g2.md` | line 536 |
|---|---|---|
| old text | `plus the two readers C1 missed` |
| new text | `plus the two SHAPES C1 missed` + a bracketed errata line enumerating all 14 guard sites, naming `:6355` as the opposite-polarity E6 reader, and stating why conflating shapes with readers let the fourteenth go unexamined |
| derivation | the two commands above | output as shown |
