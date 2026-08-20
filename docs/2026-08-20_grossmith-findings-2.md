# grossmith differential findings — 2026-08-20 (campaign 2)

Second grossmith campaign, run against the `bugfix-arc` tip `9b9ea712`
(the audited merge candidate, tree clean). Successor to
`docs/2026-08-07_grossmith-findings.md`, whose three items are all
disposed (BUG-042 fixed, the exit-code sharp edge fixed, both corpus
promotions landed). Same conventions: minimal repro inline, controls
run on the same path, hypothesis stated, disposition proposed.

**This document is a findings RECORD only.** The branch is post-audit,
so nothing here is fixed on it: every actionable item is filed in §9 as
an owed follow-up with its minimized program inline. No corpus row, no
`BUGS.md` entry, no baseline move is made by this commit.

**One-line summary.** 79,800 judged programs produced **3 observation
mismatches and 2 reference build failures**. Of those five: **one is
ours** (a forced-point wrong answer that widens open BUG-062 from
`len`/`cap` to `min`/`max` — §1), **three are gc's** (one arithmetic
miscompilation, two assembler refusals — §2, §3), and **one is
latitude** (an unsequenced point where gc realizes a different
conforming member than our deterministic pin — §4). The differential
oracle was wrong more often than the machine was.

---

## 0. Campaign parameters

| | |
|---|---|
| Generator | `deps/grossmith` @ **`e68867d`** (clean; recorded as `cwd-git:e68867d6a61061ead0922703ce58d1c7a461b3b8`) |
| Clone under test | `golean@9b9ea7124607678824e6f38ca2797bb017a09769` (this branch tip, clean worktree) |
| Reference oracle | `go version go1.26.5 linux/amd64`, `/usr/local/go/bin/go`, sha256 `8da5fd32…c67f9`, module mode |
| Clone nested oracle | the SAME pinned binary via grossmith's PATH shim, `GOPATH (GO111MODULE=off)`; `scripts/diff-coverage` sha256 `9cec625d…cbd65` |
| Panic equivalence | `golean-harness (expected status + exact panic message)` |
| Capability profile | `golean.Profile`: slices+maps leave the OBSERVED tier (still legal as feeders); constructs `observe_point`, `defer`, `recover` excluded; `recover_wrapper` deliberately kept |
| Budgets (recorded in each `batch.json`) | run 10s, build 2m, lake build 20m, subject output cap 8 MiB, clone log cap 16 MiB, identity 30s |
| Memory cap | `GOLEAN_MEM_MAX=24G`, every invocation through `scripts/capped` |
| Artifacts | `artifacts/grossmith-2026-08-20/` (gitignored) |
| Wall clock | main leg 4 batches, 23:47→00:59 (~72 min); legs 2+3 ~25 min |

Batches, all published and re-verified offline with `gengo -verify`
(**every case-input digest intact and bound to the manifest; report
bound; report self-consistent; clone tree bound** — 5/5):

| batch | mode | cases | seed range |
|---|---|---|---|
| `m1a` | swarm | 20,000 | 1000000–1019999 |
| `m1b` | swarm | 20,000 | 2000000–2019999 |
| `m1c` | swarm | 20,000 | 3000000–3019999 |
| `m2pairs` | `-pairs 20` (pairwise construct coverage) | 19,800 | 4000000–4019799 |
| `arch386` | `-clone gc-386`, no golean profile | 4,000 | 1000000–1003999 |

`m2pairs` ran the pairwise rung: 45 of 48 optional tags in the pair
universe (the profile excludes 3), **850/990 pairs realized at least
once**.

### 0.1 Verdict counts, per the tool's closed taxonomy

Main leg (m1a+m1b+m1c+m2pairs), **79,800 cases, 79,798 reference-ran**:

| verdict | count |
|---|---|
| `match` | **79,795** |
| `observation-mismatch` | **3** |
| `reference-infra-failure` | **2** |
| `clone-infra-failure` | **0** |
| `harness-error` | 0 |
| `both-infra-failure` | 0 |

Secondary counters: 16,499 panic paths, 5,533 wrapper-caught panics of
which **5,533 wrapper-JUDGED** (caught == judged + clone-infra, exactly
— the accounting identity holds).

**The zero in `clone-infra-failure` is itself a result.** Across 79,798
judged programs the native frontend refused nothing: no
`frontend-export` gap, no `stuck`, no `unsupported`, no `lean-run`
failure. Every program in grossmith's generated subset of Go reached a
semantic verdict. (Scope: the subset is bounded — see §8.)

### 0.2 Where the five non-matches went

| case | batch | verdict | channel | §|
|---|---|---|---|---|
| `case_15642` | m1b | observation-mismatch | **ours** (widens BUG-062) | §1 |
| `case_10480` | m2pairs | observation-mismatch | **gc-bug** | §2 |
| `case_09214` | m1a | reference-infra-failure | **gc-bug** | §3 |
| `case_02834` | m2pairs | reference-infra-failure | **gc-bug** | §3 |
| `case_16162` | m2pairs | observation-mismatch | **latitude** (reading I-2) | §4 |

---

## 1. OURS — `min`/`max` are not ordered events, so calls hoist past their operands

**This widens open BUG-062 from `len`/`cap` to the value-returning
built-ins, and adds a second observable (panic ORDER) to the existing
one (wrong value).** It is not a regression from this arc: it is the
same root cause, on a shape the corpus never had.

### 1.1 The spec, verbatim

`deps/go/doc/go_spec.html` @ `go1.26.5` (the pinned language version):

> **Order of evaluation** — "…when evaluating the operands of an
> expression, assignment, or return statement, all function calls,
> method calls, receive operations, and binary logical operations are
> evaluated in lexical left-to-right order."
>
> "However, the order of those events compared to the evaluation and
> indexing of `x` and the evaluation of `y` and `z` is not specified,
> **except as required lexically. For instance, `g` cannot be called
> before its arguments are evaluated.**"

> **Built-in functions** — "Built-in functions are predeclared. **They
> are called like any other function** but some of them accept a type
> instead of an expression as the first argument."

> **Min and max** — "The **built-in functions** `min` and `max`
> compute the smallest—or largest, respectively—value of a fixed
> number of arguments of ordered types."

Chaining these: `min` is a built-in function; built-ins are called like
any other function; therefore a `min(...)` at lexical position *i* is
an ordered call and must be called before any call at position *j > i*;
and by the "except as required lexically" clause it **cannot be called
before its own arguments are evaluated**. So everything `min` reads is
read before the later call runs. Forced. No latitude.

### 1.2 Minimal repro — the panic-order axis (from `case_15642`, seed 2015642)

The generated case's psite-13 statement was
`v1, v6, _ = int8(0), min((v12+uint8(12)), v11[v0]), wit(((v0+v0)+(-v0)), 9)`
with `v0` far past `len(v11)`. Hand-minimized to:

```go
package main

var w int

func wit(x int, tag int) int { w = w*31 + tag; return x }

// min is the lexically first CALL; wit is the second. min must be
// called before wit, and min cannot be called before its arguments are
// evaluated -- so s[i] panics BEFORE wit runs, and w is 0.
func probeBuiltinArgIndex() (r int) {
	s := "abc"
	i := 100
	defer func() { recover(); r = w }()
	var a byte
	var b int
	a, b = min(byte(1), s[i]), wit(7, 9)
	_, _ = a, b
	return -1
}
```

Manifest row (strict lane):
`builtin-arg-index\t<dir>\tprobeBuiltinArgIndex\t-\tok\torder\t-\tstrict\t-\t-`

Result: **`FAIL … differential`, Lean `9`, Go `0`.** The machine ran
`wit` first; gc evaluated `min`'s operand first, as the spec requires.

### 1.3 Minimal repro — the VALUE axis (silent wrong answer)

The same defect with no panic anywhere, so nothing is visibly unusual:

```go
package main

var n int

func bump() int { n = 5; return 0 }

// min is called before bump, and min reads n before it is called:
// the spec-forced answer is 1.
func probeMinValueOrder() int {
	n = 1
	return min(n, 100) + bump()
}
```

Result: **`FAIL … differential`, Lean `5`, Go `1`.** A silent wrong
answer at a forced point. `max` behaves identically (Lean `5`, Go `1`).

### 1.4 The probe matrix — what is and is not affected

Eleven probes, all on the same harness invocation path, `go1.26.5` vs
the machine at `9b9ea712`:

| probe | shape | gc | machine | result |
|---|---|---|---|---|
| `bare-index` | `s[i], wit()` | 9 | 9 | PASS — index alone is genuinely unordered; both realize the same member |
| `user-arg-index` | `idb(s[i]), wit()` | 0 | 0 | PASS — an ordinary call IS an ordered event |
| `b1-call-in-builtin-arg` | `min(1, f()), g()` | 33 | 33 | PASS — calls INSIDE a built-in's args are hoisted in lexical order |
| `b3-append-arg-index` | `append(xs, s[i]), wit()` | 0 | 0 | PASS — `append` IS treated as an ordered event |
| `b4-conversion-control` | `int(s[i]), wit()` | 9 | 9 | PASS — a conversion is not a call; unordered, and both agree |
| **`builtin-arg-index`** | `min(b, s[i]), wit()` | 0 | **9** | **FAIL** |
| **`b2-max-arg-index`** | `max(b, s[i]), wit()` | 0 | **9** | **FAIL** |
| **`b5-builtin-nested`** | `sink(min(b, s[i]), wit())` | 0 | **9** | **FAIL** |
| **`c1-min-value-order`** | `min(n,100) + bump()` | 1 | **5** | **FAIL** (value axis) |
| **`c2-max-value-order`** | `max(n,-100) + bump()` | 1 | **5** | **FAIL** (value axis) |
| `c3-len-value-order` | `len(s) + grow(&s)` | 1 | 3 | FAIL — **BUG-062's own shape, reproduced**; rig sanity check |

### 1.5 Diagnosis

`b1` PASSes, so the frontend *does* descend into a built-in's argument
list and hoist the calls it finds there in lexical order. `b3` PASSes,
so `append` is already in the ordered-event set. What is missing is
`min`/`max` themselves: with no call inside their arguments, nothing
about a `min(...)`/`max(...)` subexpression is treated as an ordered
event, so it stays inline while a later call is hoisted ahead of it —
and everything the built-in reads (a global, a bounds check) is then
read late.

This is the **same predicate gap BUG-062 names**, which `docs/BUGS.md`
and the queued mini-slice A6 currently describe on the `len`/`cap`
axis only ("inline `len`/`cap` reads reorder against calls"). The
campaign shows the gap is not about *reads* and not about `len`/`cap`:
it is that **the ordered-event predicate does not enumerate the
value-returning built-ins**. A6's stated scope is therefore
known-incomplete, which is the one thing in this document that should
travel with the merge ask (§9, F-1).

`c3` reproducing BUG-062's own shape on this rig is the control that
says the rig is measuring what it claims to.

---

## 2. GC-BUG — a 32-bit truncation in an optimized constant fold

`case_10480` (m2pairs, seed 4010480). **Our machine is right and gc at
default flags is wrong.** This is the finding the metamorphic leg
exists to make findable, and it arrived through the main leg.

### 2.1 How it was localized

The observation differed in exactly one of 15 values (`q0`, an `int`):
machine `8217745495067144867`, gc `3894218945028886963`. The subject was
instrumented with a tap after every top-level statement and re-run
through the differential; the first divergence was at tap 20, and the
delta was **exactly 2^32**.

### 2.2 Minimal repro — 11 lines

```go
package main

func tf0(p0 int) (int, int) {
	p0 = (p0 >> 4) - max(p0>>31, max(p0, -51))
	return ((p0/-2147483648)*(p0/-10) + (-p0)), max(p0>>3, p0<<6) * -2147483648
}

func main() {
	a, b := tf0(-54)
	println(-4 + a*31 + b) // want 2147483737
}
```

```
go1.26.5 linux/amd64, default flags : -2147483559   <-- WRONG (2^32 low)
go1.26.5 linux/amd64, -gcflags=all=-N  : 2147483737
go1.26.5 linux/amd64, -gcflags=all=-l  : 2147483737
go1.26.5 linux/amd64, -gcflags=all='-N -l' : 2147483737
```

Hand derivation: `p0 = -54` → `(-54>>4) = -4`, `max(-54>>31, max(-54,-51)) =
max(-1,-51) = -1`, so `p0 = -4 - (-1) = -3`. Then
`a = (-3/-2147483648)*(-3/-10) + 3 = 0*0 + 3 = 3` and
`b = max(-1,-192) * -2147483648 = -1 * -2147483648 = 2147483648`.
`-4 + 3*31 + 2147483648 = 2147483737`. gc **prints `a=3` and
`b=2147483648` correctly** and then computes the final sum 2^32 low.

### 2.3 Characterization

- Suppressed by **either** `-N` **or** `-l` — so it needs inlining
  *and* the optimizer; adding `//go:noinline` to `tf0` also makes it
  disappear.
- Not the `prove` pass: `-gcflags=all=-d=ssa/prove/off` still miscompiles.
- Independent of microarchitecture level: `GOAMD64=v1/v2/v3` all wrong.
- Making the input opaque (`-54 * len(os.Args)`) makes it disappear —
  consistent with a **constant fold after inlining that truncates to
  32 bits**.

### 2.4 Whole-program confirmation

On the unmodified generated case, `go run -gcflags=all='-N -l'`
produces an observation document that differs from the default-flags
one in **exactly one value**, and that value is
`8217745495067144867` — **byte-identical to what our machine
produced**. The machine matched unoptimized gc on all 15 values.

This is a `gc-bug` in the sense of `docs/spec-divergence-ledger.md`,
Regehr-class, and it is a concrete instance of the 2026-08-20 doctrine
sharpening already recorded there ("gc is NOT definitionally
legitimate Go"). It is also a live reminder for the corpus: a
differential FAIL is not automatically ours.

---

## 3. GC-BUG — a legal program gc refuses to assemble ("offset too large")

Two cases, `case_09214` (m1a, seed 1009214) and `case_02834` (m2pairs,
seed 4002834), classified `reference-infra-failure` — the harness
refused them *before* the clone, so the machine never saw them and
nothing was misattributed. Both fail identically:

```
<autogenerated>:1: offset too large in 00699 (…/subject.go:143)
	MOVB	SIB, main..autotmp_100+2147483682(SP)(R12*1)
```

The programs are legal Go (`go vet` type-checks them; only style
warnings), and **both compile cleanly under `-gcflags=all='-N -l'`**.
The defined behaviour is a runtime index-out-of-range panic; gc instead
fails at assembly time on an unencodable stack displacement above 2^31.

### 3.1 Minimal repro — 25 lines

```go
package main

func tf1(p0 int, p1 int) (int, int) {
	for i1 := 0; i1 < 4; i1++ {
		p0 = 55
	}
	return (-(p0 / 3)), (p1 % -2147483648)
}

func tg1(xs ...int) int {
	acc := 0
	acc = acc*31 + xs[0]
	acc = acc*31 + xs[1]
	return acc
}

func fuzzSubject() int {
	v0 := 2147483647
	v14 := []int8{-60, 57, 24}
	v0 += tg1(tf1(v0, ((v0 << 33) & (v0 >> 32))))
	v14[v0] = (v14[2] % int8(-128))
	return v0
}

func main() { _ = fuzzSubject() }
```

```
default flags        : offset too large in 00107 … MOVB BL, main..autotmp_14+2147483652(SP)(AX*1)
-gcflags=all=-l      : offset too large (still)
-gcflags=all=-N      : compiles
-gcflags=all='-N -l' : compiles; runs; panic: runtime error: index out of range [2147483089] with length 3
GOARCH=386           : compiles
```

So it is the optimizer (`-N` suppresses it), not inlining. Folding the
index to a syntactic constant by hand (`v0 += -558`) does **not**
reproduce — the constant has to arrive through the SSA pipeline, which
is why the reducer plateaued at 25 lines rather than 5.

Same family as §2 in the loose sense that both are amd64 constant
handling near 2^31; **stated as a hypothesis, not a claim** — they were
not root-caused to a shared pass.

Rate: 2 in 79,800 generated programs (~1 in 40,000).

---

## 4. LATITUDE — a failing type assertion is not ordered against calls

`case_16162` (m2pairs, seed 4016162). **Not a bug on either side.**

The panicking statement was
`v13, _ = (v16.(T0) * (v13 * v13)), wit(max(wit(v0, 4), wit(59, 5)), 6)`
with `v16`'s dynamic type not `T0`. The order witness read `0` under gc
and `4005` under the machine — and `4005 = ((0*31+4)*31+5)*31+6`, i.e.
the machine ran all three `wit` calls before the assertion panicked,
while gc panicked first.

`spec#Order_of_evaluation` orders only "function calls, method calls,
receive operations, and binary logical operations". A type assertion is
none of these, and here nothing lexically requires it before the `wit`
calls (they are not its arguments). So the order is **not specified** —
which under adopted reading **I-2** (`docs/spec-interpretations.md`,
backed by ledger `L-013`) means UNSEQUENCED, and both realizations
conform.

Isolated probes:

| probe | shape | gc | machine | reading |
|---|---|---|---|---|
| `d1-assert-vs-call` | `iv.(T0), w(max(w(1,4), w(59,5)), 6)` | 0 | 4005 | unspecified — both conforming |
| `d2-assert-as-call-arg` | `sink(iv.(T0), w(7,9))` | 0 | 9 | also unspecified: `w` and `sink` are ordered (`w` first, being inner), but nothing orders the assertion against `w` |

Note the contrast with §1, and it is the whole point: in §1 the
non-call operation is an **argument of a lexically earlier call**, and
the "except as required lexically" clause forces it; here it is a
sibling operand and nothing forces it. `bare-index` in §1.4 is the same
latitude point on the indexing axis, where gc happens to realize the
machine's member.

gc is **self-stable** here (default and `-N -l` agree), so this is
latitude in the spec, not instability in gc.

**Disposition: an inventory entry, not a fix.** The machine's
deterministic pin is a legal member; what the campaign adds is a second
witnessed axis (type assertion; and by `bare-index`, indexing) for the
UNSEQ point already recorded for the implicit-`&` receiver probe.
Filed as F-3 in §9.

---

## 5. Metamorphic leg — gc against itself

New this campaign. Each sampled case was run three ways and the emitted
`grossmith-observation-v2` documents compared byte-for-byte:

- **A** default flags,
- **A′** default flags again (control: separates *inherent*
  nondeterminism from *compilation-mode* instability),
- **B** `-gcflags=all='-N -l'`.

| sample | cases | stable | run-unstable | optmode-unstable | infra |
|---|---|---|---|---|---|
| `m1a` stride 20 | 1,000 | 1,000 | 0 | 0 | 0 |
| `m1b` stride 40 | 500 | 500 | 0 | 0 | 0 |
| `m2pairs` stride 40 | 495 | 495 | 0 | 0 | 0 |
| `m1c` stride 4 | 5,000 | 5,000 | 0 | 0 | 0 |
| **total** | **6,995** | **6,995** | **0** | **0** | **0** |

Read this honestly:

- **The stride samples found nothing**, and that is the expected
  outcome at this rate. Only §2 is a *run-mode* instability, so the rate
  this sampler is actually hunting is **1 in 79,800**; 0 hits in 6,995
  is exactly what that predicts. (The §3 class is a *compile-mode*
  instability, 2 in 79,800, and the sampler would have booked it as
  `infra`.)
- **The leg's two real classes came through the main leg's full
  population**, not through the samples: §2 was found because the
  differential flagged it and the metamorphic comparison then decided
  *which side* was wrong, and §3 was found because every case is
  compiled at default flags by the reference pass. Both were then
  confirmed metamorphically (`-N -l` compiles / gives the other answer).
- So the leg's demonstrated value in this campaign is **as an
  attribution instrument, not as a sampler**. The 0-run-unstable column
  is nonetheless a real result: it corroborates grossmith's
  STRICT-lane outcome-determinism claim over 6,995 programs.
- A cheaper, higher-yield shape for next time: metamorphic **compile**
  checks over the whole population (which is what caught §3 for free)
  rather than metamorphic **run** checks over a sample.

---

## 6. Cross-arch leg — the degenerate clone (`gc-386`)

4,000 cases at `GOARCH=386` against the same gc at `amd64`, run
**without** the golean capability profile (so slices, maps, `defer` and
`recover` are all live — a wider surface than the main leg):

```
match 3130 | observation-mismatch 870
cross-arch discrimination: divergences in-tag 870, off-tag 0 over 4000 judged cases
width_dependent-tagged 3493;  width_dependent yield: 870/3493 (24.9%)
```

**Zero off-tag divergences.** Every cross-arch difference fell inside
grossmith's declared `width_dependent` quotient. This is the harness's
own discrimination control and it passed: the taxonomy separates a real
divergence from a declared one, which is what makes the main leg's
3-in-79,800 believable rather than a tuning artifact.

---

## 7. Known-gap cross-check

The campaign was checked against `baselines/native-full.tsv`,
`docs/BUGS.md`, `docs/2026-08-19_triage-table.md`,
`docs/language-coverage-ledger.md`, `baselines/untriaged-ids` and
`docs/2026-08-11_latitude-inventory.md`.

### 7.1 Overlap with the known-red set

**None.** No mismatch landed on any of the 12 bug-pinned fidelity ids,
the 11 dispositioned `untriaged-ids` rows, or the 108
`frontend-export` reds.

The `wrong-answer` ratchet in `baselines/untriaged-count` is unchanged
at **0**, but be precise about why: that ledger ratchets **baseline
reds**, and §1 has no corpus row, so it was never in the denominator.
The mechanical count is untouched; the *claim* the count stands for —
"no forced-point divergence lacks an explanation" — survives only
because §1 *is* explained, by open BUG-062's root cause. It is not
evidence that no unexplained wrong answer exists, and if F-2's rows are
promoted the ratchet will need three new red pins attributed to
BUG-062. §2/§3 are gc's and §4 is latitude, so neither touches the
class.

### 7.2 The arc's fresh work — what this campaign can and cannot say

Coverage is quantified from the judged tag histogram over 79,798 cases,
so each claim below is anchored to how much the shape was actually run.

| arc item | exercised? | evidence |
|---|---|---|
| **BUG-062** (`len`/`cap` vs call) | **YES** — `len` in 24,108 cases | Not regression evidence: the campaign **widened** it (§1). The `c3` probe reproduces BUG-062's own shape. |
| **BUG-063** (receiver-position implicit `&*q`) | **NO** | The generator emits no pointers at all (no address-of, no `*T`, no pointer receivers). **No regression evidence either way** — do not read the clean sweep as covering it. |
| **BUG-005 / the map-range envelope** | **NO** | Maps appear in 40,338 cases but the generator emits map range only as an order-invariant fold (`map_range_fold`, 14,088), never under mutation, and the golean profile keeps maps out of observed positions. **The envelope is untouched by this campaign.** |
| **The 19 arms** — family 1 (`[]rune`/`string([]rune)`) | **NO** | no rune conversions in the generator |
| — family 2 (slice→array conversion) | **NO** | construct not generated |
| — family 3 (IEEE `min`/`max` over floats) | **NO** | no floats in subjects. *Integer* `min`/`max` are exercised in 36,719/36,703 cases, and that is where §1 came from. |
| — family 4 (array-pointer index / nil deref) | **NO** | no pointers |
| — family 5 (struct tag pointer conversion) | **NO** | no pointers |
| — family 6 (`go` of a nil func) | **NO** | no goroutines |
| **BUG-042** (defined-type inc/dec — campaign 1's find) | **YES** — `defined_types` in 40,446 cases, `incdec` a live construct | **Clean. This is real regression evidence** that campaign 1's fix holds at scale. |

### 7.3 Clean sweeps worth stating (the ledger's thin spots)

The research map flagged three areas as having *no* `BUGS.md` entry and
thus being the likeliest places for genuine news. All three were
exercised heavily and came back **clean**:

- **switch / break / continue** — `switch` 32,184, `break` 10,568,
  `continue` 10,511, `unreachable_case` 17,961, `default` 32,184.
- **three-index slice expressions** — `slice_triple` 1,748.
- **integer conversion and overflow at defined types** —
  `conversions` 36,156, `boundary` 79,683, `corner_boundary` 9,960,
  `corner_kinds` 10,019, `widths`/`width_dependent` 79,800/72,353.

Also clean at scale: `interfaces` 22,724, `methods` 20,525,
`assertion` 9,735, `type_switch` 1,938, `append` 18,584, `delete`
16,177, `comma_ok` 11,280, `tuple_forward` 18,298, `string_index`
7,877, `string_slice` 8,752, `string_range` 3,785, `concat` 12,001,
`recover_wrapper` 13,592 — of which 5,533 actually caught a panic, and
all 5,533 of those reached a semantic verdict.

The honest framing: this is a strong **lower-bound** result over the
generated subset — observed ∈ modeled on 79,795 programs. It is not an
upper-bound argument anywhere, and at the two latitude points it
touched (§4) `go run` witnessed one member and nothing about envelope
width.

---

## 8. What this campaign did NOT cover

Stated so the clean sweep is not over-read. Measured, not assumed: the
subject sources of 3,000 m1a cases (271,871 lines) were scanned with
fixed-string and anchored patterns.

**Absent, count zero:** unary `&` and unary `*` — so no pointers, no
address-of, no dereference (every `&` in the corpus is binary bitwise
AND); `chan`, `select`, `go`; `float`, `complex`; `rune`; `unsafe`;
`goto` and labels (all 3,070 `IDENT:` lines are `default:`); generics
(no type parameters, no `~`); `import` (subjects are import-free, so no
stdlib); `range`-over-func; anonymous struct types; `func init`.

**Present, and therefore genuinely exercised** — worth naming because
two of them are easy to assume away: the `recover_wrapper` shape emits
a **deferred function literal closing over mutable locals and named
results** (`defer func() { if recover() != nil { q17 = psite; … } }()`,
13,592 of 79,800 cases), and the `order_witness` shape emits a
**package-level `var wOrd int`** mutated by a helper. Method
declarations with value receivers, named interface types, and `any`
slots are all present too.

Under the golean capability profile the campaign additionally emits no
`defer`/`recover` outside that wrapper shape, and keeps slices and maps
out of observed positions.

Consequently **every concurrency-, pointer-, float- and
package-structure-related open item in `docs/BUGS.md` and the frontier
ledger is untouched by this campaign** — including BUG-002, BUG-004,
BUG-008, BUG-014, BUG-041, BUG-059, BUG-061 and all 15 FR rows. A clean
sweep here says nothing about them.

---

## 9. Owed follow-ups (nothing fixed on this branch)

**F-1 — widen BUG-062's statement and mini-slice A6's scope.**
`docs/BUGS.md`'s BUG-062 entry and A6's queued scope both describe the
defect as inline `len`/`cap` reads. §1 shows the real predicate gap is
that **the ordered-event set omits the value-returning built-ins**, and
that it is observable both as a wrong value and as a wrong panic order.
Owed: amend BUG-062's text (or open a sibling entry) and re-scope A6 to
enumerate built-in call sites, with `append` recorded as already
correct so A6 cannot regress it. **This is the one item that should
annotate the merge ask** — not block it (BUG-062 is already open and
red-pinned on this branch; the arc introduced nothing here), but the
A6 scope as written is known-incomplete and a reader should learn that
from the record rather than from the next campaign.

**F-2 — corpus promotion offer (5 rows, all corpus-ready).** The §1
probes are already in corpus shape (import-free `main.go`, one subject
function each, gofmt-clean). Suggested pins, colors as measured:

| suggested id | subject | color now |
|---|---|---|
| `builtins/min-max-vs-call-order/min-value` | `probeMinValueOrder` | RED (differential) |
| `builtins/min-max-vs-call-order/max-value` | `probeMaxValueOrder` | RED (differential) |
| `builtins/min-max-vs-call-order/min-arg-panic` | `probeBuiltinArgIndex` | RED (differential) |
| `builtins/min-max-vs-call-order/append-arg-panic` | `probeAppendArgIndex` | GREEN — the control A6 must not regress |
| `builtins/min-max-vs-call-order/call-in-builtin-arg` | `probeCallInsideBuiltinArg` | GREEN — the control that says arg-call hoisting already works |

`probeBuiltinArgIndex` and `probeMinValueOrder` are inline at §1.2 and
§1.3; `probeMaxValueOrder` is the `max(n, -100)` variant of the latter.
The two GREEN controls, which are the rows that stop A6 from
over-reaching, in full:

```go
var b1, b3 int

// GREEN control: a user CALL inside a built-in's argument list. The
// frontend already hoists these in lexical order -- min's arg call
// runs before the later call, so w=1*31+2=33 on both sides.
func witB1a(x int) int { b1 = b1*31 + 1; return x }
func witB1b(x int) int { b1 = b1*31 + 2; return x }
func probeCallInsideBuiltinArg() int {
	_, _ = min(1, witB1a(5)), witB1b(6)
	return b1 // 33 on gc AND on the machine
}

// GREEN control: append is ALREADY an ordered event, so its operand's
// panic precedes the later call. A6 must not regress this to the
// min/max behaviour.
func witB3(x int, tag int) int { b3 = b3*31 + tag; return x }
func probeAppendArgIndex() (r int) {
	s := "abc"
	i := 100
	xs := []byte{1}
	defer func() { recover(); r = b3 }()
	var a []byte
	var b int
	a, b = append(xs, s[i]), witB3(7, 9)
	_, _ = a, b
	return -1 // 0 on gc AND on the machine
}
```

The probe trees as run are in
`artifacts/grossmith-2026-08-20/machine-probe/{order,order2,order3}/main.go`
with their manifests beside them.

**F-3 — latitude inventory entry for the UNSEQ non-call-operand axis.**
§4 witnesses the same unsequenced point already recorded for the
implicit-`&` receiver probe, now on the **type assertion** axis (gc
realizes the other member) and the **indexing** axis (`bare-index`, gc
realizes ours). Owed: one inventory row naming the axis, with the note
that no strict row should pin it. Deliberately **not** a corpus case.

**F-4 — two `spec-divergence-ledger` entries, kind `gc-bug`.** §2 (the
2^32 constant-fold truncation) and §3 (the "offset too large" assembler
refusal), both with the minimized programs above and the flag matrices.
Both are Regehr-class and both are upstream-reportable; §2 additionally
belongs in the record as the first campaign case where **the
differential oracle, not the machine, was the wrong side**.

**F-5 — a grossmith-side note (external project, not ours to patch).**
The tool's STRICT lane promises outcome-determinism by construction and
pins gc's realization as the expected answer, but it emitted programs
whose observable outcome sits at an unsequenced point (§4). That is a
lower-bound-only claim, correctly so, but the `order_witness` construct
can land on latitude points as well as forced ones. Worth handing back
to grossmith as an observation; **no patch was made to `deps/grossmith`
and none should be** (trust-tools rule).

---

## 10. Replay

Everything is seed-deterministic and every batch re-verified offline.
From the grossmith checkout (`deps/grossmith` @ `e68867d`, clean):

```sh
export ART=<repo>/artifacts/grossmith-2026-08-20
export GOCACHE=$ART/go-build-cache

# regenerate + re-judge any main-leg batch (~18 min each, 32 workers)
GOLEAN_MEM_MAX=24G <repo>/scripts/capped \
  go run ./cmd/gengo -n 20000 -seed 2000000 -out $ART/m1b \
    -clone golean:<repo>

# the pairwise batch
GOLEAN_MEM_MAX=24G <repo>/scripts/capped \
  go run ./cmd/gengo -pairs 20 -seed 4000000 -out $ART/m2pairs \
    -clone golean:<repo>

# the cross-arch discrimination control
GOLEAN_MEM_MAX=24G <repo>/scripts/capped \
  go run ./cmd/gengo -n 4000 -seed 1000000 -out $ART/arch386 -clone gc-386

# a single case, byte-for-byte, from its case.json alone
go run ./cmd/gengo -replay $ART/m1b/case_15642
go run ./cmd/gengo -replay $ART/m1a/case_09214

# offline integrity + self-consistency of a published batch
go run ./cmd/gengo -verify $ART/m1b
```

Verified during this campaign:

```
replay case_15642: subject byte-identical (sha256 a04d7a1d9bf3), features identical (25 tags)
replay case_15642: observation byte-identical to the batch record
replay case_09214: subject byte-identical (sha256 264eefe476b5), features identical (35 tags)
replay case_09214: SAME FAILURE CLASS as the record (build-failed) — source reproduced
```

The three findings' seeds, for the record: **`case_15642` = seed
2015642** (§1), **`case_10480` = seed 4010480** (§2), **`case_09214` =
seed 1009214** and **`case_02834` = seed 4002834** (§3), **`case_16162`
= seed 4016162** (§4).

The metamorphic and probe drivers used here are
`artifacts/grossmith-2026-08-20/{metamorphic.sh,reduce.py}` plus the
`machine-probe/manifest*.tsv` rows, all under the gitignored artifacts
tree; they are scaffolding, not tracked instruments.
