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
