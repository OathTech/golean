# Examples phase-2 — pre-merge adversarial audit and fix round (2026-08-15)

The audit the merge protocol requires (CLAUDE.md §"THE AUDIT CHECK"), run
against the arc's **final state** — branch `phase2` at `8101b726`, the
comparator-landmark tip — and the record of the fix round that answered
it. Three decorrelated reviewers, one dimension each, pointed at primary
sources (the tree, the gate scripts, `#print axioms` output, the corpus
records) rather than at our conclusions; every surviving finding was
independently verified before it reached this list.

**What this document is, precisely.** It is the DISPOSITION record: what
was found, what was fixed here, what merges as a recorded gap. It is not
a transcript of the three reviewer reports — findings appear under the
identifiers they were verified with (`A-*`, `B-F*`, `C-H/M/L*`), at the
granularity the fix round consumed them.

## The dimensions, and what each returned

| dimension | scope | outcome |
|---|---|---|
| **A — gate and trust surface** | `scripts/ci`'s new steps, the statement-TCB closure, the designation's import pins, the memory-cap wrapper | 1 MAJOR, 1 MINOR — both fixed |
| **B — claims, pins and artifacts** | every quantitative claim in the gallery and the slice records against the measurements; axiom pins vs what is pinned; the new macro's guard | 9 findings — all fixed |
| **C — records, structure and design** | charter/slice-record coherence, module layering, the promotion ledger, attributions | findings graded HIGH (`C-H1`…`C-H7`), MEDIUM (`C-M1`…`C-M8`) and LOW (through `C-L12`) — fixed here or recorded below |

**No finding was against a theorem statement or a proof.** Nothing in the
fix round touches either: the corrections are to gates, records,
docstrings and attributions, plus one strengthened macro guard, one
deleted lemma with zero consumers, and three added axiom pins. The
in-build `Audit` gate's pins are byte-identical across the round.

## Findings and dispositions

### A — gate and trust surface

| id | finding | disposition |
|---|---|---|
| A-MAJOR | The seven `Examples/*Program.lean` lowerings entered the Comparator Challenge's TRUSTED import closure (via `Examples/Targets.lean`) with **no import pin of their own**, and Targets' own allowlist admitted them behind a `[A-Za-z]+Program` wildcard — so a new import inside any of them, or a new `*Program` module, was unreviewed trusted surface. | **FIXED** (`scripts/ci`): a `check_surface_imports … '^import GoLean\.'` pin per module, all seven verified core-only before pinning; the wildcard replaced by the seven names spelled out. |
| A-MINOR | The cap→`LEAN_NUM_THREADS` parser matched the `*M` suffix before validating digits, so a malformed `GOLEAN_MEM_MAX` reached `$(( … ))` — bash evaluates the text as an arithmetic expression and prints a raw shell diagnostic instead of the documented fallback note. | **FIXED**: digit guard hoisted above the suffix branches; behaviour checked across `64G/48G/8192M/500M/bare-bytes/empty` and `abcM/64.5G/infinity/none`. |

### B — claims, pins and artifacts

| id | finding | disposition |
|---|---|---|
| B-F1 | Gallery, reverse fuel bound: called `335 + 205·n` "the measured law … tight at the measured points". It is a valid affine BOUND; the true counts are not affine (first differences alternate 167/242, one two-pointer swap every other iteration) and it is tight only at `n = 0`. | **FIXED** — bound framing, no "measured law". |
| B-F2 | Same claim, slice-1 record: "tight at even `n`" — false at four of the five even points. | **FIXED**, with the gaps stated. |
| B-F3 | wordcount envelope `206·n + 314` described as tight at `n ≤ 3`; correct range is `1 ≤ n ≤ 3` and the first differences are 218, 206, 206, 194. | **FIXED** in the gallery, the theorem docstring and the slice-1 record. |
| B-F4 | minmax **Ground** paragraph lacked reverse's wrap-region disclosure. | **FIXED**: no corpus row reaches the `uint64` wrap region (the differential driver parses `int64`); the wrap behaviour was checked in this audit **machine-side only, with no `go run` oracle in the loop** — explicitly weaker than reverse's `go run` probes. Driver extension recorded as arc input E1. |
| B-F5 | `derive_entry_eq`'s `#eval`-before-`decide` guard compared two `Except` values, so two runs both ending `.error .fuelOut` compare EQUAL — a vacuous pass. Its docstring also claimed a mis-derived layout fails "never in the kernel", which a single-point probe cannot promise. | **FIXED** both halves: the probe now asserts the machine-entry run is `.ok` before comparing; the docstring says what a single-point check does and does not buy. |
| B-F6 | `unsafe` / `opaque` / `@[implemented_by]` were scanned by nothing — they let compiled behaviour diverge from logical content, and `#print axioms` cannot see it. | **FIXED**: new declaration-anchored preflight step, one allowlist entry (`proofs/GoLeanProofs/EntryEq.lean`) carrying its reason. Speedbump standard. |
| B-F7 | Three theorems named in the gallery as "kept with their pins" had none: `reverse_readout_v1`, `minmax_readout_v1`, `minmax_framed_readout`. | **FIXED**: three `#guard_msgs #print axioms` pins added, each `[propext, Classical.choice, Quot.sound]` as verified. |
| B-F8 | `8101b726`'s message says the judge ran from a clone of "THIS COMMIT"; the certified commit is `e42020397648`, its parent. | **FIXED**: precision note in the landmark log. The recording commit's own delta is docs plus a comment-only `proofs/Audit.lean` change (verified), so nothing certified moved underneath the run. |
| B-F9 | slice-2 record §3: the Gcd retrofit row said 37 → 10 lines; the true counts are 34 → 11. | **FIXED** — and the recorded net (`−44`) is what exposes it: `(30−9) + (34−11) = 44`. |

### C — records, structure and design

Fixed in this round:

| id | finding | disposition |
|---|---|---|
| C-H1 | Charter still carried slice 1 as **PARTIAL — proof half not landed** after all three swaps landed. | **FIXED**: DISCHARGED annotation naming `3fbecfa2` / `3f4835ba` / `67917d97` and the designation `e4202039`; the original text kept as history. |
| C-H2 | slice-1 record header made the same stale claim and its navigation pointer sent readers to a section that is not the end of the record. | **FIXED**: header reads COMPLETE; pointer names the later sections and the closure. |
| C-H5 | The three swapped examples' ROOT modules do not reach their own designated headline: `import GoLeanProofs.Examples.Reverse` (…`MinMax`, …`WordCount`) does not give you `reverse_ok` / `minmax_ok` / `wordcount_ok`, which live in the swap shards. | **PARTIALLY FIXED — see "The C-H5 constraint" below.** The requested re-export is not expressible: each shard imports its root, so the root importing the shard is a cycle. Docstrings now say where the headline lives and what to import; the structural repair is a recorded follow-up. |
| C-H6 | The charter's 48G claim had not been re-checked at the arc's final state. | **FIXED**: re-confirmed and recorded — `scripts/ci` PASS at `GOLEAN_MEM_MAX=48G` (`LEAN_NUM_THREADS=6`) at the fix-round tip. |
| C-H7 | Charter lever-5 row described a cache key the commit did not ship, and implied an acceptance measure the commit says cannot be taken locally. | **FIXED**: the row now records the re-designed three-layer key and states the lever is landed and UNMEASURED (a cache-hit measurement needs a real runner and two pushes). |
| C-M2 | "generalized to `N`" was claimed for `storeTarget_arrayLocal_u64`, which was already `N`-generic where it stood; the lemma the lift genuinely generalized is `normalizeValueForTy_arr8_u64` → `_arr_u64`. | **FIXED** in the module docstring and the promotion ledger. |
| C-M3 | The ledger's `goArr8` non-lift reasoning reads as current but was superseded by the designation hoist. | **FIXED**: annotated — both copies now live in `Examples/Targets.lean`, the two-defs conclusion stands and is re-justified in `e4202039`. |
| C-M4 | `stepFn_call_enter` recorded at 3 consumers; it has 4 (MinMax/HarnessR was missed). | **FIXED** in both slice records. |
| C-M6 | Four gallery prose attributions named `proofs/Audit.lean` or the root example module where the quoted block comes from a shard. | **FIXED**: gcd, binsearch, isort axiom attributions → their `Audit/*.lean` shards; the isort family → `InsertionSort/Family.lean`. |
| C-M7 | The trust section named only `fibHarness_pin` and "its six siblings", which for the three swapped examples pin the DEMOTED harnesses. | **FIXED**: the current headline pins named with their locations (`Audit/Reverse.lean:61`, `Audit/MinMax.lean:62`, `Audit/WordCount.lean:110`) alongside the `_v1` pins. |
| C-M8 | slice-1 record placed `maxMultiplicity` / `multiplicity` in `Pure.lean`; post-hoist they live in `Examples/Targets.lean`. | **FIXED** at both mentions, plus a closing note listing what the hoist moved. |
| C-L1 | `wcFamily_take` had zero consumers. | **FIXED** — deleted (the one sanctioned deletion of this round). |
| C-L5 | WordCount's shard table omitted `HarnessR`, the shard carrying the designated headline. | **FIXED** (with its import direction stated). |
| C-L8 | Two dangling charter references: `harness-style-scoping.md §10.5` and "sweep report §5". | **FIXED**: the ruling is §10 open decision 5; the "sweep report" names no document in this repo and the pointer was dropped. |
| C-L9 / C-L10 | `Examples/Targets.lean` says "seven gallery headlines" (there are eight over seven examples — fib has two); `e4202039` counts the hoist at 18 defs where the file holds 20. | **FIXED**: the docstring says eight over seven; the count discrepancy is recorded in the slice record (the two same-named `goArr8` defs are counted once in the commit message). |
| C-L12 | The gallery's arc-record pointer named the founding arc only. | **FIXED**: phase-2 charter first, founding arc named after it. |

### The C-H5 constraint (found while fixing it)

The fix as scoped — the three roots import their swap shard so
`import GoLeanProofs.Examples.<X>` reaches the designated headline —
**cannot be applied as stated**: `Reverse/HarnessV.lean`,
`MinMax/HarnessR.lean` and `WordCount/HarnessR.lean` each begin with
`import GoLeanProofs.Examples.<X>`, so the root importing the shard is an
import CYCLE, which Lean rejects. Making it acyclic means either moving
theorems (forbidden in an audit-response round) or splitting each root
into a `Core` shard with the root demoted to an aggregator — the shape
`WordCount` already has from slice-0 lever 2, and a ~4,600-line verbatim
move for `Reverse` + `MinMax` that also re-points gallery verbatim
markers.

What was done instead: each root's docstring now states plainly that the
designated headline lives in the swap shard, which imports the root, and
that the shard is the module to import to reach it. The aggregator
`proofs/GoLeanProofs.lean` imports all three shards, so nothing is
outside the audited build. **The structural repair is a post-merge
follow-up** (below), and it is the same work as C-H4.

## Merging as recorded gaps — the post-merge follow-up list

Nothing here is a fail-open: each is a known, written-down state, not a
gate that passes while something is wrong.

1. **C-H3 — import pruning.** Example and proof modules carry imports
   wider than they use. Mechanical, but it moves what is in each
   module's closure, so it belongs in a change reviewable as such.
2. **C-H4 — module DAG repair**, of which **C-H5's structural half is
   part**: `Reverse` and `MinMax` roots split into `Core` shards so the
   root can aggregate its swap shard and `import …Examples.<X>` reaches
   the current headline. Gallery verbatim markers move with it; do it
   when those modules are next open.
3. **C-M1 — re-privatization.** Names that lost `private` to the
   slice-0 lever-2 split (Lean's `private` is per-module) and are no
   longer referenced across a shard boundary should get it back; the
   slice-2 sealed-API contracts are the standard to re-apply.
4. **C-M5 — the "byte-identical"/"VERBATIM" claims** made by the split
   and hoist commits deserve a mechanized check rather than review
   alone; today they are recorded assertions.
5. **Remaining LOW findings** not itemized above: cosmetic and
   cross-reference drift, each below the threshold at which fixing it
   is cheaper than reviewing the fix.
6. **E1 — the differential driver's `int64` argument limit**, which is
   why no corpus row reaches the `uint64` wrap region for reverse or
   minmax. Already recorded as a frontend-arc input in the charter;
   repeated here because two gallery entries now cite it as a limit on
   their evidence.
7. **The comparator-judge worktree bug, still owed onward** (recorded
   at the landmark, `docs/2026-08-02_comparator-judge-sprint.md`):
   `scripts/comparator-judge`'s closure walk does `f="${f//.//}"` over
   the whole path, so any repo root containing a dot — every
   `.claude/worktrees/<lane>` — aborts fail-closed with a fake "missing
   module". One-line fix; owed to the next arc that touches the judge
   wrapper, and it is what forced this arc's landmark to run from a
   dot-free clone.

## Fix-round commits and gates

Three commits, in this order:

1. **gate fixes** — A-MAJOR, A-MINOR, B-F6, B-F5 (code half), C-L1.
2. **doc/gallery fixes + this record** — B-F1…B-F4, B-F5 (doc half),
   B-F7…B-F9, and the C-level corrections above.
3. **C-H5** — the root docstrings, per the constraint recorded above.

`scripts/ci` PASS under `GOLEAN_MEM_MAX=48G` after each; `render-gallery`
green (every edit is outside the verbatim blocks, which are byte-checked
against their sources). The differential corpus is untouched by this
round — no runtime code changed — so the full 1560-case record recorded
at `cba113c` still stands.
