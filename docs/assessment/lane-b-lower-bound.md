# Lane B — lower-bound audit (C2: observed ⊆ modeled)

[AGENT] fidelity-assessment lane B worker, 2026-08-31. Branch
`fidelity-assessment`. Plan: `docs/2026-08-31_fidelity-assessment-plan.md`
§Lane B. Everything below is evidence-anchored (file:line or a probe run
this session; probe sources under `artifacts/laneb/`, gitignored).
Grading vocabulary per phase 0: STRONG / ADEQUATE / WEAK / ABSENT.

## Summary

C2's evidence machinery is in much better shape than the plan's prior
suggested in some places and thinner in others. The observation channel
is NARROWER than the plan's "stdout/exit?" guess — program stdout is not
observed at all; the channel is (status class, deep-reflected subject
RESULT values, first panic/fatal line) — and its narrowness is enforced
by fail-closed refusal at three independent layers, not by corpus
convention (probed live this session). The allocator quotient's
condition (pointer-equality-only surface) therefore holds mechanically
today, but no tripwire ties an observation-surface widening back to
register #6 — and the fmt refusal message actively invites the wrong
fix. The oracle matrix is honestly one gc version on one 64-bit
platform, but the repo has already institutionalized `-race` as a second
oracle mode, has a mechanical version pin with a recorded float
incident behind it, and — the largest under-weighted fact — has a
PROVEN generative-fuzzing instrument (`deps/grossmith`, successor to the
retired `side/gofuzz` prototype) whose second campaign judged 79,800
generated programs in ~72 minutes and found the ORACLE wrong more often
than the machine (3 gc bugs vs 1 ours). That instrument is not
integrated into any cadence and its generator excludes exactly the
surfaces where the model is riskiest (pointers, floats, channels/
goroutines, defer, generics, stdlib). Overall C2 grade this lane
supports: **ADEQUATE, with a clear upgrade path** — the top-5 items
below are what separates it from STRONG.

## Top 5

1. **B10 (REOPEN, M) — fuzzing is the proven highest-yield C2
   instrument and is unintegrated.** Two campaigns ever, run by hand;
   generator covers no pointers/floats/concurrency/defer/stdlib —
   precisely the machinery (channels, sync, race, BUG-063's pointer
   class) the hand corpus alone now guards. Cadence integration is S;
   generator widening is M; concurrent-program generation is L and
   design-gated.
2. **B8 (ESCALATE = the standing P5 decision) — a second
   implementation is the ONLY possible oracle for two claim classes:**
   Go-realizability of unexhibited membership-set members (today
   "too-wide has no oracle" is a permanent epistemic hole, stated
   in-script), and gc-realization-vs-Go-semantics at every pinned
   latitude row (E3/E5/E7, R15, hidden-dep-order). Neither gccgo nor
   tinygo is installed (verified); the campaign doc already designed
   the lane (§4.5) and left the go/no-go at P5 — that memo is owed.
3. **B3 (REOPEN, S) — the allocator quotient's condition is guarded
   by construction but not by cross-reference.** Register #6's
   discharge is conditional on the pointer-equality-only surface;
   the three refusal sites that enforce the condition (fmt verb/kind
   matrix, harness reflect encoder, machine observation decoder) do
   not name the quotient, and the fmt refusal text says "widen with a
   differential pin first" — for `%p` that is an instruction to
   re-open the theorem silently.
4. **B4+B13 (REOPEN, S/M) — the strict lane's nondeterminism tripwire
   is shallow and lane routing is by hand.** Three fixed 8–10-entry
   choice streams, exhaustion defaulting to pick 0
   (`State.lean:156-160`), are the only mechanical check that a
   hand-classified strict row is actually schedule/iteration
   insensitive; a choice-hungry program can sit green in the strict
   lane as a single-run equality.
5. **B5+B6 (REOPEN, S) — the oracle-matrix cheap legs are unbuilt:**
   a per-point-release drift census (GOLEAN_ALLOW_GO_DRIFT is already
   the loud mechanism; the 1.26.x float incident and the L-014
   three-toolchain matrix show both the need and the method), and the
   64-bit-int scope caveat owed at Value.lean since the inventory
   (R1 "no site-level caveat — owed") plus in the C2 claim's own
   wording ("Go 1.26 on 64-bit platforms").

Unanticipated findings the coordinator should know: (a) grossmith
campaign 2's headline — *the differential oracle was wrong more often
than the machine* (3 gc bugs, 1 ours, in 79,800 programs) — reframes
gc from ground truth to bounded-trust witness, strengthening the case
for version sweeps and a second implementation as arbitration
instruments; (b) the plan's "parked side/gofuzz … revival costs"
framing is stale — side/gofuzz was retired 2026-08-07 and superseded
by the external `deps/grossmith` project, which is alive and pinned
per campaign; (c) program stdout is entirely outside the observation
channel (narrower than the plan assumed), which makes several
"unobservable" arguments stronger than recorded; (d) the certified-
record rot surface is one file (a single tier=slow row survives the
POR slice), re-certified nightly.

---

## 1. The observation channel

### B1. What is actually compared (the channel map)

**Evidence.** `scripts/diff-coverage:475-556` (status classification),
`:691-722` (machine run + `observation-eq`), `:103-140`
(panic/fatal extractors); `tools/coverageharness/main.go:380-476`
(the Go-side reflect encoder); `GoLean/CLI.lean:122-250` (machine
encoder), `:397-441` (`decodeObservation` + `observation-eq` =
structural JSON equality after strict decoding).

The compared observation per case is exactly:

- **Status class**: `ok | panic | deadlock | race | fatal` (manifest-
  declared, checked on both sides). Machine-only statuses
  (`unsupported | stuck | error | fuel-out`) exist and can NEVER pass
  (`CLI.lean:414`, `diff-coverage:696-707`).
- **ok**: the subject function's RESULT VALUES, deep-reflected into a
  canonical JSON tree: bool; integer with KIND (10 concrete kinds,
  width+signedness, value range-checked at decode —
  `CLI.lean:296-326`); float32/64 as exact BIT PATTERNS with NaN
  canonicalized to the one quiet NaN on BOTH encoders and signed zero
  preserved (`CLI.lean:103-120`, harness `main.go:405-423`); string as
  a byte array (no encoding ambiguity); arrays elementwise; structs as
  (typeName, ordered fields); interface boxes as (dynamic type NAME,
  value) with unnamed dynamic types refused (`main.go:449-456`); nil.
- **panic**: gc's FIRST `panic: ` line, extracted and compared as the
  exact message string (`diff-coverage:103-115,537-549`); the
  manifest's `expected_reason` additionally gates the run. Stack
  traces, goroutine dumps, everything after line 1: discarded.
- **fatal**: first `fatal error: ` line (tab-indented continuation
  accepted for fatals during panic unwinding) + the child's
  `exit status 2` report checked (`:512-535`).
- **deadlock / race**: FIXED canonical messages; the TSan report body
  (addresses, stacks) is deliberately discarded (`:490-511`).
- **Exit code**: `ok` requires go-run success and machine exit 0
  (`:708-711`); beyond the class, exit codes are not compared.

Equality is `observation-eq`: strict fail-closed decode (exact keys,
unknown tags/statuses/kinds refused) then structural equality
(`CLI.lean:422-441`).

**C2 impact.** The channel is value-faithful and deliberately narrow:
runtime ERROR STRINGS *are* in the channel (first panic/fatal line,
compared verbatim against the pinned gc), float FORMATTING is bypassed
entirely (bit patterns, not decimal strings — "Go's shortest-
representation printing stays outside the trust surface",
`CLI.lean:142-144`), and program stdout does not exist as an
observable. Every green row certifies agreement on exactly this
surface and no more.

**Verdict: KEEP.** The narrowness is a strength for C2 (it makes the
compared thing precise); the honest cost is that C2 is certified
*relative to this surface* — which is why B2/B3 matter.

### B2. Real-Go observables OUTSIDE the channel — and what enforces avoidance

For each, the enforcement is a fail-closed refusal, NOT corpus
convention; I probed the three load-bearing ones live:

| observable | avoidance mechanism | evidence |
|---|---|---|
| pointer text `%p` | fmt desugar quarantines the DECL (`unsupported` in the wire; calling it → `frontend-quarantined` → stage `frontend-export` FAIL) | **probe**: `artifacts/laneb/pverb` → `"verb %p is outside the modeled fmt subset (modeled: %d %x %s %v %+v %q %t %%)"` |
| `%v` over a pointer | verb×kind matrix refusal | **probe**: `"fmt.Sprintf verb %v over an argument of type *int is outside the modeled verb/kind matrix"` |
| pointer-typed result | harness reflect default arm fails closed | **probe**: `{"status":"error","message":"unsupported Go observation kind ptr"}` — an `error` status can never satisfy any expected_status |
| `uintptr` | refused on BOTH sides, asymmetrically on purpose (frontend maps uintptr→uint64, so a kind-visible channel must not alias them) | `main.go:403-404`, `CLI.lean:300-303`, `NativeToIR.lean:62` |
| slice/map/chan/func results | harness default arm fails closed; machine renders diagnostic-only shapes that can never equal a Go observation | `main.go:473-475`, `CLI.lean:154-228` (comments state this per arm) |
| program stdout/stderr (fmt.Println etc.) | fmt.Println is unmodeled → per-decl quarantine (`effectisolation_test.go`, `emit.go:768,909`); AND any stray go-side output corrupts the harness JSON → "Go output is not a valid observation" FAIL (`diff-coverage:482-484`) |
| float decimal formatting | `%v`/float verbs refused | **probe**: `"verb %v over an argument of type float64 is outside the modeled verb/kind matrix"` |
| NaN payload/sign | canonicalized on BOTH encoders, with the revisit condition NAMED at both sites ("if math.Float64bits ever enters the supported surface … fail closed on NaN-payload-observing programs") | `CLI.lean:103-110`, `main.go:405-416` |
| timing, goroutine IDs, GC/finalizers, os/env, runtime introspection | not expressible: the stdlib surface is a closed shim allowlist — strings{Fields,Join,…}, errors.New, strconv.FormatUint…, slices.SortFunc, cmp.Compare, the fmt subset, binary.LittleEndian.{Uint64,PutUint64} (explicit byte math, so no host-endianness observable) — everything else quarantines | `tools/nativefrontend/stdlibshim.go:149-199` |
| map iteration order | IS modeled (the `mapIter` choice site) — inside the channel via the choice tape, checked by the 3-stream invariance loop (strict) or enumeration (membership/confluent) | `State.lean:274`, `diff-coverage:766-784` |
| pointer EQUALITY | in-channel and in-language; the zero-size-address latitude here is a recorded PINNED row (R15: machine = never-same singleton, gc probed non-single-valued), sitting in the untriaged `latitude` class | `docs/2026-08-11_latitude-inventory.md:1121-1135`, `baselines/untriaged-count` (latitude 4) |

**C2 impact.** A fixture that leaks an out-of-channel observable
cannot be green — the avoidance is mechanical. This is the right
fail-closed shape: the channel can only widen by someone deliberately
adding an arm on both sides.

**Verdict: KEEP** — with the B3 caveat below on what happens at that
deliberate widening.

### B3. The allocator quotient's condition and its guard

**Evidence.** Register #6 (`docs/2026-08-11_essence-of-go-doctrine.md:143-156`):
the `nextAddr` allocator discharge is "CONDITIONAL on the modeled
observation surface (pointer equality only): an address-exposing
channel (`%p`, pointer order, `unsafe`) re-opens it." Inventory C11
carries the matching RE-OPENING CONDITION
(`docs/2026-08-11_latitude-inventory.md:460-464`). What mechanically
guards the condition today is the B2 refusal set — three independent
fail-closed default arms (fmt verb parser, harness reflect encoder,
strict observation decoder).

**The gap.** None of the three enforcement sites cross-references
register #6 or C11. Worse, the fmt matrix's refusal message
instructs: *"fail closed — widen with a differential pin first"*
(probe output, `fmtdesugar.go`). For `%d` that instruction is
correct; for `%p` it is precisely how the quotient gets re-opened
without anyone noticing — a differential pin of `%p` output would
"pass" (addresses would just never match, or worse, a normalization
would get invented) while silently invalidating
`Frame.allocatorIndependence`'s scope. Contrast the NaN
canonicalization, which names its revisit condition AT the code site
on both sides — that is the model to copy.

**C2 impact.** Today: none — condition holds. Forward risk: the one
recorded quotient discharge whose validity depends on the channel
staying narrow has no tripwire on the channel.

**Verdict: REOPEN (S).** One small change set: (i) a pinned refusal
test asserting `%p`, `%v`-over-pointer, pointer/uintptr results, and
`unsafe` stay refused, whose name and comment cite register #6/C11;
(ii) amend the fmt refusal text for address-shaped verbs to name the
quotient instead of inviting the pin.

### B4. The strict lane's nondet tripwire is shallow

**Evidence.** Strict rows re-run under exactly three fixed adversarial
streams — `"9,8,7,6,5,4,3,2,1,0"`, `"1,3,5,7,9,2,4,6,8,0"`,
`"5,5,5,5,5,5,5,5"` (`diff-coverage:766-784`). `Choices.consume` on an
exhausted stream yields pick 0, the canonical default
(`GoLean/GoCore/State.lean:152-160`). So for any program consuming
more than 8–10 choices, the "adversarial" streams converge to the
default trajectory from that point on. Lane assignment
(strict vs membership/confluent) is a hand decision per manifest row;
the per-lane caption in-script is honest ("strict … structurally
BLIND to scheduling", `diff-coverage:350-370`), but the caption is not
a mechanism.

**C2 impact.** A hand-misclassified strict row whose schedule- or
iteration-sensitivity only manifests past the stream prefix is
certified by a SINGLE gc run vs a near-default machine run — the
exact single-stream point-mass the membership lane was built to
escape. 2,204 of 2,306 passing rows are strict.

**Verdict: REOPEN (S/M).** Cheapest honest fixes, in order: (S) derive
the invariance streams' length from the machine's own choice
accounting (the accountant `stepNeeds` inventory already exists in
CLI.lean) or add a seeded-random long stream, recorded in meta; (M) a
periodic spot audit that runs the membership enumerator in
`|set|=1?`-mode over a sample of strict rows (the confluent machinery
already does exactly this check) to catch misrouted rows.

## 2. The oracle matrix

### B5. gc version sweep

**Evidence.** The pin is now mechanical at three layers:
`baselines/go-oracle-pin` (go1.26.5) enforced with a loud
`GOLEAN_ALLOW_GO_DRIFT=1` escape (`diff-coverage:147-170`), a ci step
(`scripts/ci:160-175`), and the workflow's exact `go-version: '1.26.5'`
whose HISTORY comment records the incident: *"'1.26.x' … still floated
WITHIN the family — go1.26.6's release moved the oracle under CI
silently (2026-08-21) … A pin that names a family is still a float"*
(`.github/workflows/lean_action_ci.yml:155-166`, noting go1.26.6 ships
7 compiler changes). Run meta durably records `go_toolchain` +
`go_drift` (`diff-coverage:226-230`). The multi-version method already
exists ad hoc: the L-014 gc miscompile was characterized against
go1.26.5 / go1.26.6 / go1.27rc3 built from source
(`docs/spec-divergence-ledger.md:437-447`).

**What a sweep uniquely catches.** (i) Message-text pins: panic/fatal
MESSAGES are compared verbatim, and those strings are gc-realization,
not spec — a point release can move them and today only the nightly
against the pinned toolchain would ever notice, at re-pin time.
(ii) Realized-point drift at pinned latitude rows: inventory U-7
states outright that "the inventory ASSUMES the version-tracking pins
actually fire on toolchain movement — believed true … not re-audited"
(`latitude-inventory.md:1229-1233`). A drift census converts that
belief into a measurement.

**Verdict: REOPEN (S).** A scheduled (or per-gc-release) full-corpus
run under `GOLEAN_ALLOW_GO_DRIFT=1` against next/previous point
release, with the diff recorded as a realization-drift census — the
mechanism, the loudness discipline, and the artifact format all
already exist; only the habit is missing.

### B6. Platform sweep (int width, endianness)

**Evidence.** The model hard-codes `int`/`uint` at 64 bits
(`GoLean/GoCore/Value.lean:32-43`) and maps `uintptr`→uint64
(`NativeToIR.lean:62`); the spec makes int width
implementation-specific. This is RECORDED: inventory R1 (class (b)
pin, "EVIDENCE: GC (amd64 = 64-bit only) … a 32-bit gc / tinygo lane
would exercise the other point", `latitude-inventory.md:880-897`) and
register extension #6 (`:1288-1296`), which also admits "no site-level
caveat yet [in Value.lean] — owed". Endianness: no host-endianness
observable exists — the only byte-order surface is the
binary.LittleEndian shim, which is explicit byte arithmetic
(`stdlibshim.go:192-199`), and `unsafe` is refused. Grossmith's
campaign-2 `arch386` leg measured the real spread: 870/4000 cases
diverge between gc-amd64 and gc-386, 100% inside its declared
`width_dependent` tag (`docs/2026-08-20_grossmith-findings-2.md` §6).

**What a platform leg uniquely catches.** Today: nothing the model
claims — GoLean models Go-on-64-bit, and a 386 oracle would
legitimately diverge on ~22% of width-tagged programs. The honest
move is not a sweep but a SCOPE STATEMENT plus the parameterization
path R1 already prices (pervasive-but-mechanical, "worthless until a
32-bit oracle lane exists" — i.e., blocked on B8).

**Verdict: REOPEN (S) for the two owed statements** — the Value.lean
site caveat R1 itself says is owed, and an explicit "64-bit platforms"
qualifier wherever the C2 claim is stated (doctrine / spec-sources
language pin). The width PARAMETER stays below-the-line (L), correctly
sequenced behind a second-implementation lane.

### B7. GOMAXPROCS and `-race` legs

**Evidence.** `-race` is already institutionalized as a second oracle
MODE, not a proposal: the racy lane's oracle is `go run -race` (TSan,
exit 66, no false positives — one red sample proves the race), and
membership sampling runs R samples plain PLUS R under `-race`
because "the -race runtime perturbs goroutine scheduling — plain go
run is a point-mass on schedule-dependent shapes; probes: 0/700 vs
6/6 orderings" (`diff-coverage:809-833,1056-1070`). The two modes are
correctly never mixed on deadlock rows (the detector doesn't fire
under -race, probed; `:373-384`). GOMAXPROCS is set nowhere
(repo-wide grep: one doctrine mention) — the oracle runs at host
default, and the value is not recorded in run meta (meta records
`jobs` but not nproc/GOMAXPROCS, `:1316-1318`).

**What a GOMAXPROCS matrix uniquely catches.** Too-narrow membership
envelopes whose witness schedules need single-P starvation or
many-P parallelism that the default+(-race) sampler never hits — the
three-way investigation rule's case (b) (`:386-391`). Cheap to add:
extra sample modes `GOMAXPROCS=1` / `=2` in `go_run_oracle`.

**Verdict: KEEP the -race discipline as-is (it is a genuine strength
of the apparatus); REOPEN (S)** for GOMAXPROCS sample modes + meta
recording of GOMAXPROCS/nproc.

### B8. Second implementation (gccgo / tinygo)

**Evidence.** Neither binary exists on this box (verified: `which
gccgo tinygo` → not found; only `/usr/local/go/bin/go` = go1.26.5);
no install performed per lane rules. The lane is already DESIGNED:
spec-truth campaign §4.5 (a diff-one-style runner over a curated
slice; "neither is an oracle, both are witnesses"; not a gate, an
evidence generator), with gofrontend/tinygo held as floating
setup-deps rows "only if P5 green-lights it"
(`docs/spec-sources.md:37`), and the P5 decision memo still owed
(memory: spec-truth-campaign).

**Assessment from knowledge (flagged as such).** gccgo lags the spec
by multiple releases (GCC's gofrontend has tracked ~Go 1.18 for
years) — usable as a semantics witness only on the older fragment;
tinygo tracks recent Go and reuses gc's frontend libraries but has a
deliberately different runtime (cooperative scheduler, partial
reflect, different runtime panic message TEXT). Consequence: a
second-impl leg cannot reuse strict message-text comparison — it
needs the coarser (status + values) observation, which the channel's
value shapes already support cleanly. That is a runner variant, not a
redesign.

**What it uniquely catches — the classes nothing else can:**
1. *Unexhibited membership members.* The in-script caption is
   explicit: membership "does NOT show unexhibited members are
   Go-realizable … too-wide has no oracle" (`diff-coverage:360-364`).
   A second implementation is the only instrument that can ever
   witness those members (24 membership + 57 confluent rows carry
   width metadata today).
2. *gc-realization mistaken for forced semantics.* Every pinned
   latitude row (E3/E5/E7 deviation debts, R15, hidden-dep-order) and
   every message-text pin is calibrated on one implementation; a
   disagreeing witness LOCATES latitude points the census may have
   missed (upper-bound value that lower-bound money buys for free).
3. *The R1 32-bit width point* (B6) — unlocked by a tinygo/gccgo-386
   leg and by nothing else.

**Verdict: ESCALATE — this is exactly the standing P5 [USER] decision,
now with lane-B evidence attached.** Recommendation to carry into the
memo: tinygo first (spec currency beats runtime fidelity for a
witness role), coarse-observation runner variant, curated slice (the
sequential value-computation corpus), M cost.

## 3. Corpus representativity

### B9. Shape of the 2,478-row corpus (measured this session)

**Evidence (probes over `Corpus/coverage/`).** 2,478 executable rows
over 1,137 exec fixtures (rows reuse fixtures with different
args/lanes) + 391 negative-lane files. Fixture size (lines of
main.go, n=1538 corpus-wide): min 3 / p25 10 / **median 17** / p75 30
/ p90 63 / p99 169 / max 400, mean 27.9. Feature tags per row
(median **4**, max 10; 135-tag vocabulary): 1 tag ×8, 2×141, 3×496,
4×778, 5×568, 6×356, ≥7 ×131. Top tags: slices 573, loops 435,
interfaces 371, indexing 360, methods/maps 299, channels 263,
pointers 230, goroutines 125, generics 122. PASS lanes: 2,204 strict
/ 57 confluent / 24 membership / 21 racy; the 172 FAILs are 143
frontend-export refusals + 17 lean-observation + 9 differential + 1
each nondet/membership/confluent (`baselines/native-full.tsv`), with
the untriaged split at coverage 11 / latitude 4 / **wrong-answer 0**
(`baselines/untriaged-count`).

**What hand-written-only misses.** The corpus is a feature-POINT
lattice: strong per feature, thin on co-occurrence (median 4 tags,
median 17 lines), with no case approaching real-world nesting depth,
aliasing graph complexity, or value sizes. This is not hypothetical:
both grossmith campaigns found bugs in exactly the co-occurrence
class — BUG-042 (`++` on a DEFINED type; the corpus had ++ and
defined types, never together — campaign 1's own note: "it appears
the current corpus never exercises `++` on a named type"), and the
BUG-062 widening (min/max × call-order,
`docs/2026-08-20_grossmith-findings-2.md` §1, "a shape the corpus
never had").

**C2 impact.** For the modeled fragment's SINGLE features, corpus
evidence is strong; for composition it is structurally weak, and the
measured fix (generation) exists.

**Verdict: KEEP the corpus as the anchored regression suite; the
composition gap routes to B10,** not to more hand-written cases.

### B10. Fuzzing: side/gofuzz is retired; grossmith is the live, proven, unintegrated instrument

**Evidence.** The plan's "parked side/gofuzz … what a revival costs"
is stale framing: `side/gofuzz` (untracked, gitignored) is the
RETIRED prototype — superseded 2026-08-07 by the external grossmith
project, left in place "pending the user's deletion call"
(`docs/2026-08-07_grossmith-findings.md` header addendum). Its own
tree confirms: BRIEF.md superseded by PLAN.md ("the generator is the
product; GoLean is its first consumer"), last HANDOFF entry
2026-08-04. The live instrument is a `deps/grossmith` reading
checkout, pinned per campaign.

Two campaigns, both yield-positive:
- **2026-08-07** (findings doc): BUG-042 (real machine bug, minimal
  7-line repro), plus the diff-coverage exit-code/stale-results sharp
  edge (now fixed — the gate-integrity block at
  `diff-coverage:45-59` descends from it), plus two corpus
  promotions.
- **2026-08-20** (findings-2): **79,800 programs, ~72 min wall; 79,795
  match; of the 5 non-matches, 1 ours (BUG-062 widening), 3 gc's
  (one Regehr-class arithmetic miscompilation — L-014, confirmed
  surviving into go1.26.6 and go1.27rc3 — and two assembler
  refusals), 1 latitude.** "The differential oracle was wrong more
  often than the machine." Zero frontend refusals in-fragment across
  79,798 judged programs. Verified replayable (`gengo -verify` 5/5
  batches).

**The gaps, in the campaign's own words** (§7.2/§8, measured over
271,871 generated lines): NO pointers (no `&`/`*` at all — BUG-063's
whole class untouched), no floats, no `chan`/`select`/`go`, no
generics, no runes, no stdlib imports, no defer/recover outside one
wrapper shape, maps never observed under mutation ("the [map-range]
envelope is untouched by this campaign"). And NO CADENCE: two runs
ever, by hand, against hand-picked tips; the fuzzer participates in
no gate and no schedule.

**C2 impact.** Generator-based differential fuzzing is not a
candidate scaling move for C2 — on this repo's own evidence it is the
demonstrated one, at ~1,100 programs/minute. But its current shape
systematically avoids the model's riskiest, most recently built
surfaces (channels/sync/race machinery; pointer aliasing), which are
covered by ~100-odd hand-written concurrency rows plus the enumerated
lanes only.

**Verdict: REOPEN (M), three ordered slices:** (a) S — cadence: a
scheduled campaign (weekly or per-arc) with pinned generator+SUT and
a findings-doc discipline (both campaigns already model the format);
(b) M — generator widening to pointers, floats, defer (already on
grossmith's own roadmap; consumer-driven per its PLAN); (c) L,
design-gated — concurrent-program generation feeding the
membership/confluent lanes (the schedule-ENUMERATION side already
exists in-machine; what's missing is program-shape generation, and
BRIEF.md's old non-goal note correctly separates it from the Choices-
generator mechanism). Disposition of `side/gofuzz` itself: the
pending [USER] deletion call — surface it in phase 3.

### B11. Negative corpus (lane-A adjacency, one line)

391 compile-rejection files run under `scripts/coverage-negative`
(go-build-based). Under full frontend delegation they attest "gc's
frontend rejects these and our pipeline agrees they're outside the
domain" — a static-semantics-BY-PROXY claim, whose honest wording is
lane A's delegation item; nothing lower-bound turns on it. KEEP,
wording owed by lane A.

## 4. The certification semantics

### B12. What a green run certifies, by mode — and the rot paths

**Evidence.** `scripts/ci:10-22,478-494` and `diff-coverage`
throughout. Plain `scripts/ci`: no oracle run — it JUDGES the cached
`artifacts/coverage/latest.tsv`, and the judgment is heavily guarded:
missing meta refuses, meta `manifest_sha256` must match the current
corpus manifest, partial runs refuse under `--diff`, no-record fails
closed unless `GOLEAN_ALLOW_NO_DIFF=1` (`ci:559-604`). `--diff`: full
re-run, go + machine per case, EXCEPT tier=slow rows which verify
against tracked certified records (wire-sha + params-string + set
content; samples and the 4-stream driver-coupling pin still run
live, `diff-coverage:1104-1143`). `--slow`: full re-enumeration of
tier=slow rows, which must reproduce the tracked record exactly
(`:1172-1190`). The nightly cron (03:17) runs `--slow`
(`lean_action_ci.yml:27-28`). Publication integrity descends from the
grossmith-§2 incident: results invalidated up-front, exit ≥2 = nothing
published, atomic per-case publish, dead workers fail closed
(`diff-coverage:45-59,314-327,1329-1341`). Baseline re-pins are
guarded both directions (worktree-vs-HEAD and HEAD-vs-HEAD~1;
PASS→non-PASS flips must sit on a BUGS.md `Cases:` line; shallow
clones fail closed, `ci:607-660`).

**The one real rot path, sized.** A certified record's wire-sha covers
the CASE + FRONTEND but not the INTERPRETER: a machine change can
move a certified enumeration set while quick `--diff` stays green,
because only the coupling pins (4 single runs) and 10 go samples
exercise the machine against the cached set. The script documents
this honestly ("machine-side envelope drift is caught there [--slow],
coupling drift is caught here", `:1104-1113`). Measured surface: ONE
record exists (`baselines/certified/imported-goose__channel__google-search.certified.tsv`,
certified 2026-08-21) — the POR slice moved every other former
slow-tier row into the fast lane via `engine=dedup` (e.g.
sched-dependent/first-come: 98,664-node state graph, checker-accepted,
≈1.35s, `Corpus/coverage/exec/goroutines/sched-dependent/cases.tsv`).
Window ≤ one nightly, on one row.

**C2 impact.** The certification vocabulary (full vs cached vs
re-certified) is explicit, machine-checked, and honestly reported in
meta; the known cache-staleness class has one member and a ≤24h
window.

**Verdict: KEEP.** This is the strongest-audited part of the
apparatus (three named incidents — grossmith §2, the 1.26.x float,
the slow-tier timeout flake — each left a mechanical guard).

### B13. What the ∀-stream lanes certify about nondeterminism

**Evidence.** The in-script epistemic captions
(`diff-coverage:350-391`) + lane implementations:
- **confluent** (57 rows): |set|=1 certified over ALL registry-point
  schedules within the declared tree (width/sites/cap/work; backedge
  canonical+k), then strict equality on the singleton; for
  `engine=dedup` rows the certified set is THEOREM-backed equal to
  `SlowObs` (`checkCertM_slowObs`) rather than DFS-cap-guarded.
- **membership** (24 rows): every Go sample (5 plain + 5 `-race`) ∈
  enumerated set; set CARDINALITY pinned (`members=n` — e.g.
  sb-chan's {1,10,11} pins 3 so SC-forbidden 00 cannot appear
  silently); driver-coupling pin ties the enumerator's copied driver
  to `native-json-run` on every run; zero-oracle passes refused;
  singleton sets refused (belongs in strict/confluent).
- **racy** (21 rows): EVERY enumerated path refuses + one TSan red
  sample; refuse-but-green-samples is a mandated three-way
  investigation, never a pass.

**What they do NOT certify** (all stated in-script, confirmed):
Go-realizability of unexhibited members (no oracle — width metadata +
envelope-width review only; B8 is the fix); anything below
registry-point granularity (the B3 abort window and sub-statement
granularity, register #5's residue — lane A/C territory); schedules
the `-race` sampler cannot reach (B7's GOMAXPROCS legs are the cheap
widening). And the lanes cover only rows someone ROUTED to them —
the router is a human (finding B4).

**C2 impact.** For declared-nondet rows the machinery is genuinely
possibilistic and fail-closed everywhere I could find a bypass to
probe; the honest boundary is exhibition (lower bound), never
realizability (upper bound). The structural risk sits in routing, not
in the lanes.

**Verdict: KEEP the lanes; the REOPENs are B4 (routing tripwire) and
B8 (the unexhibited-member oracle).**

---

## Verdict table (for the phase-3 synthesis)

| # | finding | verdict | cost |
|---|---|---|---|
| B1 | channel map: status + reflected results + first panic/fatal line | KEEP | — |
| B2 | out-of-channel observables all fail-closed (probed) | KEEP | — |
| B3 | quotient condition has no cross-reference tripwire; fmt message invites the wrong fix | REOPEN | S |
| B4 | strict-lane 3-stream invariance shallow; lane routing by hand | REOPEN | S/M |
| B5 | version-drift census unbuilt (mechanism exists) | REOPEN | S |
| B6 | 64-bit scope caveat owed at Value.lean + in claim wording; width param stays below-line | REOPEN | S (param: L) |
| B7 | GOMAXPROCS sample modes + meta recording | REOPEN (keep -race discipline) | S |
| B8 | second implementation = only oracle for membership width + pinned rows | ESCALATE (= P5 memo) | M |
| B9 | corpus = feature-point lattice; composition weak, measured | KEEP (fix via B10) | — |
| B10 | grossmith proven, unintegrated; generator misses pointers/floats/concurrency | REOPEN | S+M (+L gated) |
| B11 | negative corpus wording | KEEP (lane A owns) | — |
| B12 | certification modes + one-row certified-cache rot window | KEEP | — |
| B13 | ∀-stream lanes honest; risk is routing not lanes | KEEP (see B4/B8) | — |
