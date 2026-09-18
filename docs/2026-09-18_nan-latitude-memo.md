# NaN latitude memo — what fixes the bits of a produced NaN, and [a] vs [b] (2026-09-18, [AGENT])

Records only, lane `records/nan-envelope-memo-0918` at main `68b261e6`; answers item (2) of the 2026-09-18 ruling record
(`docs/2026-08-31_qrow-rulings.md`; [USER] Mike, verbatim, relayed by the [AGENT] coordinator — cite as relayed): «the
choices I suppose are either [a] pass a parameter saying what the platform says, or [b] try to provide one uniform
nondetermnism right? I think this depends on what hte Go standard says». Sites: inventory R7 and §11 (the two contracts;
`docs/2026-08-11_latitude-inventory.md`), BUG-094 (`docs/BUGS.md`). Probe evidence: `docs/evidence/2026-09-18_nan-latitude-memo/`
(go1.26.5 linux/amd64, the oracle pin). Nothing below is applied; §6's text changes are PROPOSED, PENDING [USER].

## 1. What the pinned Go spec fixes (go1.26.5, `deps/go/doc/go_spec.html`)

- spec#Numeric_types: `float64` is «the set of all IEEE 754 64-bit floating-point numbers» — set membership only.
- spec#Floating_point_operators: «The result of a floating-point or complex division by zero is not specified
  beyond the IEEE 754 standard; whether a run-time panic occurs is implementation-specific.» Fusion is permitted.
- spec#Arithmetic_operators: operators «yield a result of the same type as the first operand» — the TYPE, not bits.
- spec#Comparison_operators: «compared as defined by the IEEE 754 standard» (so `NaN != NaN`; no bit is compared).
- spec#Conversions: float↔float «rounded to the precision specified by the destination type»; if «the result type
  cannot represent the value the conversion succeeds but the result value is implementation-dependent».
- spec#Constants / spec#Representability / spec#Constant_expressions: «there are no constants denoting the IEEE 754
  negative zero, infinity, and not-a-number values»; «constant values never result in an IEEE negative zero, NaN, or
  infinity»; `3.14 / 0.0` is «illegal: division by zero». Every NaN in a Go program is a RUN-TIME value (gc's SSA
  folder agrees: `generic.rules:124–181` fold `c op d` only when `c op d == c op d`).
- spec#Min_and_max: «if any argument is a NaN, the result is a NaN»; commutativity «assuming all NaNs are equal» — ONE NaN value.

**Findings.** The spec is SILENT on which NaN an operation produces, on payload propagation, on the sign of a NaN, and on
the bits of `math.NaN()` (its doc: «returns an IEEE 754 “not-a-number” value»; 0x7FF8000000000001 is the unexported `uvnan`,
`deps/go/src/math/bits.go:8,:31`; `Float64bits` is a pointer cast, `math/unsafe.go`). Where it speaks it DEFERS to IEEE 754.

## 2. What IEEE 754-2019 permits (cited from knowledge — no copy under `deps/papers`; verify at ratification)

§6.2: an operation with quiet-NaN inputs «shall deliver as its result a quiet NaN» (the one «shall»); §6.2.1: quiet = first
bit of the trailing significand set (bit 51 / bit 22); §6.2.3: a single NaN input «should» propagate its payload; with two,
the result «should» carry one of them and «this standard does not specify which»; §6.3: «this standard does not interpret
the sign of a NaN»; §7.2: an invalid operation's default result «shall be a quiet NaN that should provide some diagnostic
information» — payload unspecified. PERMITTED SET for any produced NaN: every quiet NaN of the format — 2·2^51 = 2^52
patterns at binary64, 2^23 at binary32. Signalling results are excluded.

## 3. What gc/amd64 does (verified, `out-opt.txt`), what softfloat does, what `FloatBits.lean` does

| operation (variables; `p`=…8000000000001, `q`=…02, `s`=SNaN 0x7FF0…01, `nq`=0xFFF8…01) | gc/amd64 bits |
|---|---|
| `math.NaN()` | 0x7FF8000000000001 |
| `0/0`, `Inf−Inf`, `Inf·0`, `Inf/Inf`, `math.Sqrt(−1)` (invalid operations) | 0xFFF8000000000000 — sign SET |
| `−(0/0)`; `math.Abs(0/0)` | 0x7FF8000000000000 |
| `p+1`, `1+p`, `p·2`, `2/p`, `1−p` (one NaN operand, either position) | 0x7FF8000000000001 — payload AND sign kept (`nq+1` = 0xFFF8…01) |
| `s+1`, `1+s`, `s+p`, `p+s` (a signalling operand) | 0x7FF8000000000001 — quieted |
| `add(p,q)` / `add(q,p)` (noinline helper, fixed operand order; same for −,·,/) | …01 / …02 — the FIRST operand's payload |
| `p+q` written inline | …02 at default optimization, …01 under `-N -l` — OPTIMIZER-DEPENDENT |
| `min(0/0, 2.5)` / `max(0/0, 2.5)`; `min(p, 2.5)`; `min(p, q)` | 0xFFFC…00 / 0x7FFC…00; 0x7FFC…01; 0x7FF8…03 (POR: OR of both) |
| float32: `0/0`; `−(0/0)`; `p32+1` (`p32`=0x7FC00001); `float32(p)`; `float64(p32)` | 0xFFC00000; 0x7FC00000; 0x7FC00001; 0x7FC00000 (low payload bit lost); 0x7FF8000020000000 (payload shifted, kept) |

`runtime/softfloat64.go` (gc's software float, softfloat ports): `nan64 = 0x7FF8000000000000` «quiet NaN, 0 payload»
(:16), `return nan64` at every NaN-producing arm (:202–:334) — no propagation, sign always clear. Other gc ports
(knowledge, NOT probed here): arm64/ppc64/s390x default 0x7FF8… sign-clear with first-operand propagation; riscv64
canonical 0x7FF8… only, no propagation. So the machine's constant IS a gc member (arm64/riscv64/softfloat); amd64 is
the port whose default carries the sign bit. `FloatBits.lean`: `nan64`/`nan32` at all eleven NaN arms (:294, :295,
:331, :333, :353–:355, :412, :425, :516, :534); `fneg64` is a bare sign flip, so the producible set is
{nan64, −nan64}; `f32to64`/`f64to32` canonicalize (so `float64(p32)` and every float32 op lose the payload);
`floatMinMaxBits` (Ops.lean:275) transcribes the amd64 POR idiom over frombits payloads but returns the default NaN
when either operand is one; `floatBitsApply` (Ops.lean:198–:209) REFUSES `*bits` of the default NaN under either sign.

## 4. Observability — R7's «unobservable in-language» is FALSE since 2026-09-04; the heading is stale

Observable: `math.Float64bits`/`Float32bits` (the [USER]-admitted `float-bits` primitive) and what is built on them —
`math.Signbit(0/0)` is `true` on amd64 (probe), `Abs`, `Copysign`, `encoding/binary`, raw `unsafe` casts. NOT observable
(probe): `fmt` `%v %g %e %f %b %x %X`, `strconv.FormatFloat`, `println` — all print `NaN`, never a sign; `==`/`!=`
(`n != n`, `any(n) != any(n)`); map keys (three NaN inserts → `len == 3`); `switch`. Honest scope line: unobservable
through arithmetic, comparison, formatting and keys; observable through the bits channel. R7's body records this
(2026-09-04/05); its heading and the floats design §4/§5 sentence «the language proper cannot observe payload or sign of
NaN» do not. The differential DOES see it: BUG-094's seven rows are `FAIL lean-observation` (`baselines/native-full.tsv:
5101–5143`) — the guard refuses where gc reports 0xFFF8… (generation), 0x7FF8… (negation), 0x7FF8…01, 0xFFFC… (min/max).

## 5. The two options against the two contracts (inventory §11: A = the language, B = `Platform.gcAmd64`)

**[a] a `Platform` parameter** (Contract B: reproduce gc/amd64 — default 0xFFF8…, single-operand payload+sign propagation
with quieting, POR min/max, payload-preserving f32↔f64). Exact for generation, negation, one-NaN propagation, min/max,
conversions. NOT exact for two NaN operands: §3's `p+q` row shows the oracle instance itself is not a function of the
program (register allocation picks the survivor), so [a] alone must REFUSE there (R6's shape) or admit a choice; and by
§11's rule matching gc's member «witnesses ONE member, not portability» — [a] says nothing for Contract A.
**[b] one uniform nondeterminism** (Contract A: the produced NaN is a tape choice over §2's quiet-NaN set). Faithful
to spec + IEEE, but the membership lane oracles by ENUMERATION (`width=B`, `golean coverage-observations`,
`docs/coverage-suite-structure.md`): a 2^52 alphabet is not enumerable, so [b] alone needs a new predicate-mode
membership check («observed bits ∈ quiet NaNs of the width») — a checker change — or its strict rows stay red.
**[a]+[b].** The RELATION models [b]: a named `ChoiceSite.nanBits` whose pick is the produced NaN, admitting every
quiet NaN. The EXECUTABLE's slot 0 instantiates [a]: the gc/amd64 rule read from NaN fields on `Platform.gcAmd64`;
at the two-NaN-operand case the executable alphabet is {0: first operand's payload, 1: second's} — a `width=2`
membership row on the existing machinery. Coherent with «no semantic choice hides in evaluator recursion»: the choice
is reified at a named site with a `canonicalSlot0` row, the platform constants sit on `Platform` beside `intBits`
(declared, not hidden), and the `FloatBits` kernel takes the NaN rule as an ARGUMENT instead of returning `nan64`.
A gc-shaped slot 0 has precedent (`appendSpill`: «extra = 0 keeps gc's deterministic point»). Executable ⊆ relation
holds; the relation is wider by design (Contract A's maximality, stated per row); the reverse is never claimed.

## 6. Recommendation ([AGENT]; PENDING [USER])

**Adopt [a]+[b].** The standard's answer is unambiguous: Go fixes nothing about NaN bits and defers to IEEE, whose payload
and sign rules are «should» — so Contract A must be [b]; Contract B needs [a]'s member as slot 0 to turn seven designed
reds into strict greens honestly; pure [a] cannot be made exact (§3 `p+q`), pure [b] costs a checker mode. **Alternative,
named:** pure [a] with an R6-style refusal at two-NaN-operand sites — the smallest change, fails closed where gc is not
a function, leaves Contract A's row a (b) pin with the obligation open.
**Proposed R7 heading** (replaces the stale one whichever way the ruling goes): «R7. NaN bit patterns produced by the
machine — (b-n) NARROWED to the default NaN {0x7FF8…, −0x7FF8…}; OBSERVABLE in-language via `math.Float64bits` since
2026-09-04, refused under `*bits` (BUG-094); re-envelope PENDING [USER], memo 2026-09-18». On adoption of [a]+[b]: «R7. …
— (a) ENVELOPED over the quiet NaNs of the width (`ChoiceSite.nanBits`); slot 0 = `Platform.gcAmd64`'s realization;
two-NaN operand order a width-2 membership alphabet; believed MAXIMAL against IEEE 754-2019 §6.2». **Proposed BUG-094
PLAN:** «R7 re-envelope per `docs/2026-09-18_nan-latitude-memo.md` §6 ([a]+[b]): `nanBits` site, Platform NaN fields,
FloatBits NaN-rule argument, guard and min/max pre-check deleted; the seven Cases rows flip FAIL→PASS; born rows §7.»

## 7. Cost (under [a]+[b])

- Rows: all seven BUG-094 rows FAIL→PASS (`canonical-nan-refused`, `nan-arith-payload-refused{,/canonical-roundtrip}`,
  `neg-canonical-refused{,/float32}`, `min-max-canonical-refused`, `roundtrip-payloads`) — PASS-direction, no Cases line.
  Born: two-NaN-operand `membership` row (both source orders, `width=2`, `why` = §3's optimizer finding); f32↔f64 NaN
  conversion (payload shift/truncation); negative-NaN propagation (`nq+1`); SNaN quieting.
- Code: `FloatBits.lean` — the eleven `nan64`/`nan32` arms take a NaN-rule argument (kernel stays total, kernel-reducible);
  `Ops.lean` — delete `floatBitsApply`'s guard (:198–:209) and `floatMinMaxBits`' default-NaN pre-check; `State.lean` —
  `ChoiceSite.nanBits` + `canonicalSlot0` row; `Platform.lean` — NaN realization fields on `gcAmd64` (D1 (a) stands: read
  as the global constant, like `intBits`). Estimate 1–2 sessions, one core writer; sequencing is ruling (1)'s (after C1).
- Wire/observer: NONE — bits are already observed through `Float64bits`; the membership lane exists.
- Records: R7 → (a) (§10 counts: (b-n) 7→6); BUG-094 → FIXED; floats design §4/§5 sentence corrected; the `FloatBits.lean`
  header's «matching gc on linux/amd64» qualified (true for R4, false today for NaN bits).
