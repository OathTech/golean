# Phase 2 — adversarial verification of lane A1's 22 KEEP verdicts

STATUS: [AGENT] assessment artifact (fidelity assessment, phase 2).
Produced 2026-08-31 on branch `fidelity-assessment`, worktree
`.claude/worktrees/fidelity`, base `main` 68045b62. Object:
`docs/assessment/lane-a1-register-latitude.md`, the 22 rows it marks
KEEP. Method: for each row, re-read the fresh argument, go to the
primary sources it cites (D = `docs/2026-08-11_essence-of-go-doctrine.md`,
L = `docs/2026-08-11_latitude-inventory.md`, and the machine code),
and try to break it — freshness, survival under the NEW goal (a
consumer-facing semantics, not the raft campaign), embarrassment by a
concrete program, and dependence on a phase-1 REOPEN/ESCALATE row.
Probes are recorded with their commands; scratch under
`artifacts/p2probe/` (gitignored).

Verdict vocabulary: **KEEP-SURVIVES** / **KEEP-WEAKENED** (survives
only with a stated condition) / **KEEP-BROKEN** (becomes REOPEN or
ESCALATE).

## Summary

| Verdict | Count | Rows |
|---|---|---|
| KEEP-SURVIVES | 9 | A1-02, A1-22, A1-25, A1-30, A1-32, A1-33, A1-34, A1-38, A1-40 |
| KEEP-WEAKENED | 9 | A1-11, A1-12, A1-13, A1-17, A1-27, A1-28, A1-29, A1-31, A1-41 |
| KEEP-BROKEN | 4 | A1-04, A1-18, A1-20, A1-21 (all → REOPEN; none → ESCALATE) |

All four breaks are **evidence-backed, not rhetorical**: one refuted by
a 20-second `go run` probe (A1-18), one refuted by the machine's own
site docstring (A1-20), one by a grep that shows a record asserting a
caveat that does not exist (A1-21), one by reading the register entry
against the inventory's own known-≠-oracle list (A1-04).

### The four breaks, ranked by stakes

1. **A1-20 (E9 residual)** — the fresh argument's premise is refuted by
   the code it describes. `Cont.mapIterK`'s envelope statement says the
   unpruned case is a **DRF (synchronized) cross-goroutine delete** —
   so C10's refusal never fires, and a spec-permitted member of the
   [USER]-ruled FULL map envelope is unrealizable. Also drags A1-47
   (the census's "positive model" row) with it.
2. **A1-18 (E8 file order)** — `go run zz.go aa.go` and
   `go run aa.go zz.go` give different initialization orders from the
   SAME go command. The claim that this is "latitude over BUILD
   SYSTEMS, not over executions of a fixed build" is factually wrong,
   and E8's revisit trigger can never fire on the divergence that
   exists.
3. **A1-04 (register #2)** — "the wording is now accurate and honest"
   is false at tip: the entry is three axes stale (E12, E13, E14) and
   its known-≠-gc enumeration omits **E13**, which L §10 itself lists
   as a known-≠-oracle deterministic point.
4. **A1-21 (E10 key retention)** — the inventory says "recorded
   transfer caveat at the site"; there is no such caveat anywhere in
   `GoLean/GoCore/`. This is the identical defect A1-24 used to REOPEN
   R1, so the two verdicts are inconsistent.

---

## Part 1 — the KEEP-BROKEN rows, in full

### A1-04 — Register #2 (sequential evaluation-order latitude pinned per axis) → REOPEN

**The KEEP's fresh argument**: "as a REGISTER ENTRY the wording is now
accurate and honest (the 2026-08-12 correction did its job); the
substance is graded at the per-axis rows A1-14/15/16. The register's
own framing survives re-derivation."

**The break — the entry is not accurate at tip.** D:113–124 reads:

> Sequential evaluation-order latitude is pinned, each axis to a
> recorded conforming point — gc's where pinnable (call-vs-operand
> order, BUG-052), OURS where gc's realization is compiler-internal
> (inter-target order, early-store-across-phase), and hidden-dep init
> order to go/types' point — with the known ≠ gc cases (E3, E5, E7)
> carried as standing deviation records queued for re-envelope.

That enumeration was written 2026-08-12. Since then the inventory added
**three sequential evaluation-order axes** the entry does not mention:
E12 (binary-operator operand order vs calls, added 2026-08-17),
E13 (non-call panicking operations vs sibling calls, added 2026-08-20),
E14 (method-call receiver vs arguments, added 2026-08-22). E4
(targets-vs-RHS) is arguably absorbed by "inter-target order"; E12/E13/
E14 are not absorbed by anything in the sentence.

The sharp half: L:1421–1425 — the inventory's own **"Known-≠-oracle
deterministic points (the honesty-critical subset of (b))"** — reads
`E3, E5, E7, E13(type-assertion axis; the indexing axis agrees),
R3(escaping path)`. Register #2's known-≠-gc list is `E3, E5, E7`.
**E13 is a sequential evaluation-order axis, is squarely in register
#2's scope, is known ≠ gc, and is missing from the register.** The
register is the doctrine's designated "honest list of every place the
machine models less than the plausible envelope"; a register whose
known-≠-gc enumeration is provably one short of the companion
document's own list is not "accurate and honest" — it is the exact
drift class the 2026-08-22 `reconcile-records` pass existed to kill,
surviving in the doctrine because that pass only swept the inventory.

**Freshness**: A1-04's argument is a re-dressed citation of the
2026-08-12 correction (it asserts the correction "did its job" and
stops). It never re-read the entry against tip. That is precisely the
failure mode phase 1's freshness rule was written to catch.

**Under the new goal**: worse, not better. A consumer-facing semantics
ships the register as its scope statement; a reader who checks
"is my program's evaluation order pinned?" gets an enumeration that
omits the axis on which gc and the machine are KNOWN to disagree.

**Verdict: KEEP-BROKEN → REOPEN.** (S, doc-only) rewrite register #2 to
cover E4/E12/E13/E14 and add **E13** to its known-≠-gc enumeration;
add a standing rule that the register's known-≠-gc list is kept in sync
with L §10's honesty-critical subset (a `reconcile-records` check,
matching the C10 check that already polices L's own enumerations).
| C2, C3, C4.

### A1-18 — E8, multi-file declaration order narrowed to the go command's file-name sort → REOPEN

**The KEEP's fresh argument**: "the spec's latitude here is latitude
over BUILD SYSTEMS, not over executions of a fixed build; pinning to
the ecosystem's sole deployed build system with a named revisit trigger
is a justified idealization for a portable semantics whose input
artifact is a go-command package."

**The break — probe.** `artifacts/p2probe/filord/`, go1.26.5 (the
pinned oracle), two files with mutually independent package-level
initializers (`var Z = note("z")` in `zz.go`, `var A = note("a")` in
`aa.go`; no dependency between them, so declaration order = file
presentation order):

```
$ go run zz.go aa.go     →  za
$ go run aa.go zz.go     →  az
$ go run .               →  az
```

The **same build system**, at the **pinned oracle version**, realizes
**both** members of E8's latitude — selected by argument order in
file-list mode. The go command sorts only in directory/package mode.
The frontend sorts unconditionally (`sort.Strings` at
`tools/nativefrontend/main.go:72` and `load.go:201`), so the machine
models exactly one member.

Three consequences:

1. **The fresh argument's premise is false.** This is not latitude over
   build systems. It is latitude over ordinary invocations of the sole
   deployed build system, exercisable by anyone who types
   `go run b.go a.go`.
2. **The revisit trigger cannot fire on the divergence that exists.**
   E8 says "revisit only if a target ships a non-go-command build."
   No non-go-command build is needed; the divergence is inside the go
   command. A trigger that cannot fire on the live class is a
   fail-open guard.
3. **`observed ∉ modeled` today** by the doctrine's own bug definition
   (D:32–35): `go run zz.go aa.go` prints `za`, and no machine stream
   produces `za` for that source set. It is not currently red only
   because the harness invokes the oracle in directory mode
   (`scripts/diff-coverage:832`: `cd "$dir" && exec go run "$@" .`) —
   i.e. the apparatus is scoped to the agreeing member, which is
   honest engineering but is *not* an argument that the other member
   does not exist.

**Under the new goal**: a consumer-facing semantics whose input
artifact is "the .go files in this directory" must say which
presentation order it models, because the same files under a different
(equally standard) invocation of the same compiler initialize
differently. Nothing in D, L, or the frontend says this today.

**Verdict: KEEP-BROKEN → REOPEN.** Minimum (S, doc + site): restate E8
as "pinned to the go command's DIRECTORY-mode presentation order
(file-name sort); the go command's FILE-LIST mode presents files in
argument order and realizes the other members — the machine does not
model them", carry the same sentence at the frontend sort site, and
replace the revisit trigger with one that can fire. Optional (M): a
presentation-order envelope, if a consumer needs file-list builds.
| C2, C3.

### A1-20 — E9 residual: cross-goroutine delete during another goroutine's range → REOPEN

**The KEEP's fresh argument**: "the argument reduces to 'every
cross-goroutine map write during a range is a race' — true at the
footprint (`mapIterK` reads the live cell every pick; a concurrent
write conflicts), so any observing program refuses before the narrowing
could show. Sound — but note it leans on A1-07's refusal completeness."

**The break — the machine's own site docstring says the opposite.**
`GoLean/GoCore/Machine.lean`, the `Cont.mapIterK` ENVELOPE STATEMENT
block (constructor at :1771), closing paragraph, verbatim:

> Residual narrowing, recorded: the delete-prune walks the DELETING
> goroutine's own continuation, so a **DRF cross-goroutine delete
> (synchronized mid-range)** does not prune other goroutines'
> in-flight produced/start sets — re-production of a cross-goroutine
> deleted-then-re-created key is not realized.

The narrowing is scoped **by the code** to the **DRF, synchronized**
shape. A race requires the delete and a pick to be HB-unordered; a
channel handshake between them orders them. So:

- The refusal never fires (there is no race to detect), hence the
  narrowing is **not** unobservable-by-refusal.
- The unrealizable behavior is a member of E9's envelope — the FULL
  literal spec envelope, [USER]-ruled 2026-08-19 ("any latitude in the
  Go spec should be supported"), under interpretation I-1 (a re-created
  key is a NEW entry, so it "may be produced during the iteration or
  may be skipped"). The machine can only skip.
- Therefore **permitted ∉ modeled on a DRF program**, in the one row
  the census holds up as its positive model (A1-47).

**Witness shape** (constructible today; no probe of the machine needed,
because the code states the conclusion): goroutine A ranges over `m`
and blocks on a channel inside the loop body; goroutine B receives the
handshake, does `delete(m, k); m[k] = v'`, signals back; A resumes. A's
`produced` set still contains `k` and was not pruned, so `k` is
excluded from candidates forever. Real Go may produce it. All accesses
are HB-ordered by the handshake, so `-race` is green and the machine
does not refuse.

**Two further findings the row's dependency claim gets backwards:**

- A1-20 says the narrowing "leans on A1-07's refusal completeness, one
  more consumer of that chain." It does not — it is **independent of**
  A1-07 and fails without it. The A1-07 dependency was inherited from
  L's E9 row ("already a data race by the race footprint's pick-time
  read, U1 now closed"), which is **wrong against the code**. The
  inventory's own founding rule — "Where records and code disagreed,
  the code was taken as truth" (L:12–13) — was not applied here, and
  phase 1 propagated the record rather than the code.
- E9's re-envelope trigger ("widen or justify at the first
  cross-goroutine-range case that is not already racy-red") has
  **already fired by construction**: the DRF shape exists, and the code
  names it.

**Verdict: KEEP-BROKEN → REOPEN.** (S) correct L's E9 residual sentence
to match the code (drop "already a data race"; the shape is DRF), and
record it in the known-too-narrow class; (S) add the corpus witness
(handshake-synchronized cross-goroutine delete-and-recreate during a
range) as a membership case so the hole is red rather than prose;
(M) cross-goroutine prune, or an explicit ruling that E9's [USER]-ruled
"full literal envelope" is scoped to same-goroutine mutation. **A1-47's
"positive model" status is conditional on this**: the census's exemplar
row currently contains a live permitted-∉-modeled member.
| C3 (and C1 for the missing witness case).

*Closure note (2026-09-02 [AGENT], Tier-5 slice t5-e9-prune): the (M)
option was taken — the pool step now applies the delete-prune to every
goroutine's in-flight frames (`pruneForeign`, Multi.lean), the corpus
witnesses landed (`maps/cross-goroutine-delete-readd/{drf,insert,racy}`),
and the gc probe showed the "unrealizable" member is gc-EXHIBITED with
one intervening insert (~87%), so the hole was observed ∉ modeled, not
only permitted ∉ modeled. Inventory E9 REOPEN → CLOSED; evidence dir
`docs/evidence/2026-09-02_e9-cross-goroutine-prune/`.*

### A1-21 — E10, `==`-equal map-key retention pinned always-replace → REOPEN

**The KEEP's fresh argument**: "a genuine two-member latitude with the
observable enumerated and version-tracked; the other member has no
witness implementation and the re-envelope is one arm when XIMPL
evidence arrives. Correctly parked."

**What survives.** The pin's *substance* is fine, and I could not
embarrass it: gc's `needkeyupdate` is true for exactly the key kinds
where retention is observable (string/float/complex/interface and
composites over them) and false where `==` implies bit-equality, so
always-replace is observationally equal to gc on every kind. The
exposure list at L:690–694 is complete against that analysis.

**The break — the record the KEEP rests on is false.** L's E10 row
asserts: "a conforming original-key-retaining implementation is outside
— **recorded transfer caveat at the site**." There is no such caveat.

```
$ grep -rn "needkeyupdate\|retention\|retained key\|stored key" GoLean/GoCore/*.lean
   (no output)
```

The site is `Machine.lean:251`, `entries.set! i (key, value)`, inside
`mapAssignValue`, whose docstring says only "normalize key and value at
the map's types, insert-or-overwrite" — no statement that the NEW key
replaces the STORED key, no statement that this is a latitude point, no
transfer caveat. `mapEntryIndex?` (`Ops.lean:1750`) carries nothing
either.

**Why this is a break and not a nit.** Phase 1 REOPENed **A1-24 (R1,
int width)** on exactly this defect and on nothing else — the pin was
declared "fine", the *record* was the failure: "§9 flag 2 … it is STILL
absent from Value.lean, meaning the singleton-narrowing rule the
project's own doctrine imposes (every pin carries a site caveat) has a
two-week-old known violation." E10 is the same class of pin (a (b)
PINNED singleton at a spec-silent point), with the same missing site
caveat, **plus** an inventory sentence that affirmatively claims the
caveat exists. A KEEP and a REOPEN on identical evidence is a verdict
inconsistency; and E10 is strictly worse than R1, because R1's record
at least says the caveat is *owed* while E10's says it is *done*.

**Under the new goal**: a consumer reading `mapAssignValue` sees an
unremarked implementation choice. The nondeterminism doctrine's
singleton-narrowing rule (F8/F15) exists precisely so that does not
happen.

**Verdict: KEEP-BROKEN → REOPEN.** (S, hours) write the site caveat at
`mapAssignValue`/`mapEntryIndex?` naming the two-member envelope, the
observable key kinds, and the transfer limit; (S, doc) correct L's E10
sentence, which currently asserts a caveat that does not exist. The
pin itself stays. Recommend the same sweep be run over every (b)/(b-n)
row's claimed site record — E10 was found by spot-check, not by a
systematic one, and the sweep is a grep.
| C3, C4.

---

## Part 2 — the KEEP-WEAKENED rows, in full

Each survives, with the named condition. Where the assessment already
stated a condition, I say whether it is met and whether it is
sufficient — several conditions are assigned to rows phase 1 marked
REOPEN, i.e. they are **unmet today**, which the summary table's
unqualified "KEEP" does not show.

### A1-11 — C1/C4/C5/C8, "believed MAXIMAL at registry granularity"

**Condition (unmet)**: A1-03's scope sentence must land. A1-03 is
REOPEN, so the four rows currently ship an unqualified maximality claim
on an unsupported foundation.

**New evidence sharpening this.** `GoLean/GoCore/NPDRF.lean`'s header,
verbatim: `NPDRFReduction` is "a DRAFT STATEMENT — no theorem in the
repo claims it, **nothing may cite it (not even as a proof target: it
is refutable as written, obstruction 4)**". L's C1 row cites it anyway
("the registry-point path set vs full interleaving is the open NPDRF
obligation"), as does C10. So the inventory violates the cited file's
own no-citation rule, and the maximality qualifier that "is doing ALL
the work" (A1-11's own words) rests on a statement that is not merely
unproved but **known wrong as formalized**.

The **envelopes** survive intact and I could not break them: each site
is demonically wide at its own granularity, each anchor is verbatim or
a correctly-identified absence-anchor, and the too-wide direction is
transfer-safe. Only the word MAXIMAL is unsupported.

**Verdict: KEEP-WEAKENED.** Condition: A1-03's (S) interim scope
sentence must be attached to every "believed MAXIMAL" in C1/C4/C5/C8 —
"maximal AT REGISTRY GRANULARITY, conditional on an UNPROVED and
currently-refutable reduction" — before the semantics ships. Second,
smaller condition: the inventory must stop citing `NPDRFReduction` in a
load-bearing position, or NPDRF.lean's no-citation rule must be
amended; today the two documents contradict each other.
| C3.

### A1-12 — C6, select clause choice weakened to possibilistic "any ready clause"

**What survives**: the finite-observation half is airtight. Every
finite observation sequence has non-zero probability under uniform
choice, so no finite differential observation distinguishes the
possibilistic model from the spec's distributional text.

**The weakening — the caveat the row proposes states the wrong
direction.** A1-12 offers "no probabilistic-liveness property is
expressible" — a *missing feature*. The real content is an
**over-approximation**: C6 is the **only** latitude row in the census
whose governing spec text is DISTRIBUTIONAL AND MANDATORY
(spec#Select_statements: "a single one that can proceed is chosen via a
uniform pseudo-random selection"). At the infinitary surface the model
admits executions — e.g. always commit clause 1 forever, starving a
permanently-ready clause 2 — that a conforming uniform-pseudo-random
implementation does not realize. So `modeled ⊄ permitted` at C6's
liveness surface. The assessment's "the envelope's SUPPORT equals the
spec's, so this direction is maximal" conflates *support-maximality*
(true, and the right claim for finite traces) with *soundness* (false
for infinite ones).

This matters under the new goal in a way it did not for a verifier: a
verifier only ever loses theorems to an over-wide model, but a
**semantics product is consulted to answer "can Go do this?"** — and on
select starvation the model answers YES where Go answers, with
probability 1, NO.

**Verdict: KEEP-WEAKENED.** Condition: the consumer caveat must state
the over-approximation and its direction — "the model admits infinite
executions (starvation of a ready clause) that conforming Go's
mandated uniform pseudo-random selection excludes; C6's envelope is
support-equal on finite traces and strictly wider on infinite ones" —
not merely that a probabilistic property is inexpressible.
| C3.

### A1-13 — C9, global deadlock pinned to gc's detect-and-classify

**What survives**: the site record is real and good — `Value.lean`'s
`GoError.deadlock` docstring names the latitude ("the detection itself
is the flagship's rendering of the spec's 'blocks forever'"), so this
is not an A1-21-class unrecorded pin. `modeled ⊆ permitted` holds (gc
detects, and gc conforms).

**The weakening — the argument's load-bearing half left with the
split.** A1-13's fresh argument is "permitted ⊆ modeled fails only at a
member with no observable content." Two problems:

1. *The hang has finite observational content for a consumer.* The
   model gives a deadlocked run a **terminal** (`.deadlock`); a
   conforming non-detecting implementation gives it no terminal at all.
   Any downstream property of the form "every run reaches a terminal"
   / "the program terminates" is TRUE in the model and FALSE under a
   conforming implementation. That is a soundness-direction transfer
   failure — the E7 class, not a null one.
2. *The old defence is homeless.* L's C9 row disposes of exactly this
   by pointing at the claim shape — "deadlock-freedom via
   `ProgressExecC` excludes the terminal". `ProgressExecC` is
   reasoning-side and left with the 2026-08-31 split; this repo
   "makes NO verification claims" (CLAUDE.md). So the semantics now
   ships a terminal whose safe-use rule lives in a parked branch. Same
   class as A1-46's dangling-evidence finding, missed there.

Minor, verified: the site docstring cites "latitude row L6", which does
not exist in the inventory (the row is C9) — stale citation, A1-46
class.

**Verdict: KEEP-WEAKENED.** Condition: the semantics must ship the
transfer sentence itself (`.deadlock` is a modeled terminal standing in
for the spec's "blocks forever"; downstream termination/progress claims
must exclude it), since the claim-shape argument that made the pin safe
is no longer in this repo. Fix the L6 citation in the same edit. The
pin itself stays — widening to "hang" is still the wrong trade.
| C3, C4.

### A1-17 — E6, `len`/`cap` hoist discriminating shapes REFUSED

**What survives**: verified fail-closed with a named cause
(`panicFreeOperand`, `tools/nativefrontend/emit.go:8528` and its use at
:7686; `wire.go:91` documents the rule), and the reach *is* calibrated
(the goose-parity F23 cliff).

**The weakening — the retirement condition A1-17 relies on is not
recorded.** A1-17's KEEP is "(retire with A1-16)" on the ground that
"Retirement condition exists (rides A1-16's mechanism)". E6's row
(L:584–594) says only that the refusal "EXISTS because realizing gc's
point inside the E3/E4 latitude needs the linearization not built" — it
names *linearization*, and §7 item 5 offers linearization OR the
panic-identity membership envelope. Whether the membership route also
retires E6 is a plausible inference, but it is **an inference, not a
record**; no sentence anywhere says E6 retires with §7 item 5.

The charter is explicit that "scaffolding carries a retirement
condition or a deletion date". A refusal that kills whole-package
export whenever an idiomatic `len(p.xs)` appears in a receive-bearing
function is expensive scaffolding to carry on an unrecorded condition
— and the condition is gated on A1-16, which phase 1 REOPENed, so it is
unmet.

I reject the second half of A1-17's argument on its own terms: "a C1
frontier fact for the feature-ladder lane, not a fidelity defect"
launders the *cause*. E6 exists **because** of an unresolved
sequential-latitude axis; reclassifying its cost as feature-ladder work
moves the accounting away from the fidelity debt that generates it.

**Verdict: KEEP-WEAKENED.** Condition: write E6's retirement condition
explicitly (it rides §7 item 5's panic-identity membership envelope,
not only the unbuilt linearization), and keep its cost accounted as
fidelity debt, not ladder debt, until that lands.
| C1, C3.

### A1-27 — R4, float fusion/extra precision narrowed to per-op rounding

**What survives — and it is the best site record in the corpus.**
`FloatBits.lean`'s "Envelope statement — fusion + extra precision"
block states the narrowing, names it a deliberate strict subset, scopes
it to "gc on linux/amd64 with default GOAMD64", gives the transfer
sentence explicitly ("gc/arm64 and gc/amd64-v3 executions of programs
containing fusable patterns … are OUTSIDE the envelope, and claims do
not transfer to them"), and names the tripwire. The tripwire fixture
`Corpus/coverage/exec/floats/fma-shape` exists. The "wrong shape for a
Choices site" argument (whole-DAG rewritings, not a per-op coin) is
sound and I could not break it.

**The weakening**: the condition A1-27 states — "the scope surfaced at
every C2 statement (A1-05's work)" — is **unmet**, because A1-05 is
REOPEN. Today the site is scoped and the global claim is not: any
sentence in D or L of the form "observed ⊆ modeled" is true only with
"on linux/amd64, GOAMD64=v1" attached, and none carries it.

**Verdict: KEEP-WEAKENED.** Condition: A1-05's platform-scope sentence
must land on the C2 claim statements. Nothing else in the row needs to
change; the site is exemplary and should be the template A1-21/A1-24
are fixed against.
| C2, C3.

### A1-28 — R5, float division by zero narrowed to no-panic

**What survives**: the site record exists (`Machine.lean`, the `.div`
arm: "Float division dispatches BEFORE the integer divide-by-zero
check: it NEVER panics — IEEE ±Inf/NaN results … an envelope narrowing
matching gc everywhere; pinned by floats/division-specials"), and gc
never panics.

**The weakening — the argument inverts the doctrine's evidence
hierarchy.** A1-28's fresh argument is "spec grants the latitude but
no conforming panicking implementation is known to exist; the narrowing
matches every observed implementation and the widening is one arm
behind XIMPL/ARCH evidence." But:

- The spec sentence is an **explicit grant**, not silence: "whether a
  run-time panic occurs is implementation-specific." Spec text is the
  doctrine's **highest** upper-bound evidence class (D:37–52).
- The doctrine states that measured gc behavior is "a lower-bound
  instrument that can also *motivate* narrowing arguments, **never
  conclude them**" (D:50–52). "No conforming panicking implementation
  is known to exist" is an absence-of-observation argument being used
  to *conclude* a narrowing at an explicit-grant point. That is the
  named forbidden move.
- Gating the widening on XIMPL puts a lower-bound instrument in charge
  of an upper-bound decision, and the cost is one arm at a site guarded
  by "the divisor is zero" (width 1 everywhere else — no enumeration
  blow-up, unlike R4).

**But a legitimate argument does exist, and the row should use it.**
The spec's own sentence anchors the *value* to IEEE-754 ("not specified
beyond the IEEE-754 standard"); IEEE-754's default non-trapping mode
mandates ±Inf, Go exposes no FP trap control, and the deployed-program
corpus depends on ±Inf arithmetic — the doctrine's **de-facto-spec**
evidence class, which is an upper-bound class in good standing. The
panic member is a legacy allowance for non-IEEE hardware Go does not
target.

**Verdict: KEEP-WEAKENED.** Condition: re-ground the justification on
the IEEE-754 / de-facto-spec evidence class (an upper-bound argument),
delete the "no known implementation" reasoning (a forbidden lower-bound
conclusion), and state at the site that the machine excludes an
**explicitly spec-granted** member. With that re-grounding the pin is
correct; without it the row is a doctrine violation that happens to
reach the right answer.
| C3.

### A1-29 — R6, out-of-range float→int conversion REFUSED

**What survives**: the refusal is real, fail-closed, and names its
cause at the site (`Ops.lean:1148–1150`,
`"float-to-int conversion out of range/NaN (implementation-dependent in
Go)"`). The latitude is genuinely cross-target divergent.

**The weakening — "the only resolution" is false, and the row has no
queue position.**

1. *Not the only resolution.* The row's fresh argument says refusing is
   "the only resolution that is neither a silent pin nor an
   unvalidatable guess". At least two others exist and are already
   in-house patterns: (a) a **two-member value envelope**
   {amd64's `0x8000…`, arm64's saturation} with per-platform membership
   rows — exactly the shape R4 uses for platform-scoped float behavior
   and R15 proposes for {0,1}; the row itself supplies both realized
   points, so an oracle exists for each; (b) an unconstrained demonic
   value choice at the site — spec-maximal (the spec grants the result
   value outright), trivially sound, validated by containment. "No
   oracle for the envelope" is true only of a *single* oracle for the
   *whole* envelope, which is not what the membership pattern needs.
2. *The spec says the conversion SUCCEEDS.* "the conversion succeeds
   but the result value is implementation-dependent." The machine
   refuses a program class that real Go always runs. That is a
   coverage hole in the product, not a fidelity idealization.
3. *No retirement condition.* R6 appears **nowhere** in §7 — neither in
   the priority queue (items 1–5) nor in the "below the line
   (recorded, deliberately not queued)" list. Compare E6, which at
   least rides §7 item 5 implicitly. A refusal with no queue position
   and no deletion date is exactly what the charter forbids.
4. *Double-booked against A1-41.* R6 is the first item in L §5, so it
   is inside A1-41's object too. A1-29 KEEPs it as a **fidelity
   disposition** ("the only resolution"); A1-41 KEEPs the same refusal
   as **C1 coverage debt** whose placement "is C1 work, not fidelity
   debt". The census carries two incompatible framings of one refusal.

**Verdict: KEEP-WEAKENED.** Condition: R6 is KEPT as a fail-closed
**coverage debt with a recorded retirement condition and a §7
position**, not as a fidelity resolution; strike "the only resolution"
(the two-member platform-membership design is available and is already
the house pattern); reconcile the framing with A1-41.
| C1, C3.

### A1-31 — R8, WaitGroup counter pinned to gc's bit layout

**What survives**: the site record is thorough — the `wgAdd` arm cites
`waitgroup.go:104/109`, the exact wrap arithmetic, and the pinning case
`sync/waitgroup-int32`. gc is the sole oracle. Transfer for
panic-freedom claims is in the safe direction (if the model does not
panic, a wider-counter implementation does not either).

**The weakening — two corrections.**

1. *"Misuse-scale deltas (≥2^31)" understates reachability.* Probe
   (`artifacts/p2probe/wg/`, go1.26.5):
   `wg.Add(1<<30); wg.Add(1<<30)` → gc panics
   `sync: negative WaitGroup counter` on the **second** statement. The
   site's own comment records it even more cheaply: "`Add(1 << 31)`
   panics in gc where the unbounded Int proceeded" — **one statement**.
   So the divergence between the pin and a conforming
   wider-counter implementation is reachable in one or two lines of
   ordinary, documented-legal Go, and it is observable as
   **panic vs no-panic** (control flow), not as a message delta.
   "Misuse-scale" reads as "unreachable"; it is not.
2. *The site presents gc-conformance at a latitude point as
   correctness.* The comment frames the arithmetic as a bug fix
   ("divergence was real in BOTH directions") and concludes "matching
   gc's bit pattern exactly", with no sentence saying the DOCS
   underdetermine this and a conforming implementation may not panic
   here. D:66–74 is explicit: "no record may present gc-conformance at
   a latitude point as correctness."

**Verdict: KEEP-WEAKENED.** Conditions: (a) correct the reachability
framing in L's R8 row — one-statement reachable, panic-vs-no-panic
observable; (b) add the transfer caveat at the `wgAdd` site, which
currently reads as a correctness claim. The pin stays.
| C3.

### A1-41 — §5, the refusals-standing-in-for-latitude list

**What survives**: I verified each named refusal individually and each
is a visible red naming its cause. Probes
(`artifacts/p2probe/{at5,uns}/`, frontend at tip):

```
sync/atomic  → "package-selector call atomic.AddInt64 (package "sync/atomic" surface not modeled)"
unsafe       → "basic type unsafe.Pointer"
%p           → refused by fmtdesugar.go:210's verb-set default arm
float→int    → Ops.lean:1148, named cause
```

The refusal *mechanism* is in good order and A1-41's framing ("this is
the C1 boundary working as designed") is right about the mechanism.

**The weakening — §5 is not a census, and A1-41 KEEPs it as one.**

1. **Count mismatch, 6 vs 9.** §5 (L:1174–1177) lists exactly six
   items: R6, E6, select-with-select rendezvous, racy programs (C10),
   uintptr observations, `go` during `$pkginit`. §10 (L:1420) states
   "REFUSED standing in for latitude: **9** (§5)." Three items are
   unaccounted for and no reader can tell which. This is the same
   membership-vs-mention defect the 2026-08-22 reading rule was adopted
   to kill — and §10's REFUSED bullet is the one bullet in §10 that
   **does not enumerate at all**, in direct violation of that rule
   ("§10 does not merely count, it ENUMERATES … Keep it that way").
2. **A load-bearing refusal is missing from the list.** C11 names two
   guard refusals — "uintptr observations refused; **pointer
   formatting unsupported**". §5 lists only the first. The `%p`
   refusal is not decorative: A1-09 identifies it as one of the three
   sites that constitute the allocator quotient's re-opening guard —
   i.e. the guard for the register's only theorem-closed entry — and
   notes that no sentence names them as the guard. It is absent from
   the refusal census as well.
3. **A listed item's site does not match its name.** "uintptr
   observations" has no uintptr-specific refusal: `uintptr` is an
   ordinary integer type in the frontend (`wire.go:563`,
   `intType("uintptr")`); what actually refuses is `unsafe.Pointer`
   ("basic type unsafe.Pointer"). The refusal is real; the census entry
   misnames its site.

**Verdict: KEEP-WEAKENED.** The refusals survive; the list does not.
Condition: (S, doc-only) make §5 an enumerated census — reconcile it
with §10's count of 9 (either name the missing three or fix the count),
add the `%p`/pointer-formatting refusal, and re-point "uintptr
observations" at its actual site. Recommend the §5 list carry the
"three refusal sites ARE the quotient's guard" sentence A1-09 asks for,
since §5 is where a reader will look.
| C1, C4.

---

## Part 3 — the KEEP-SURVIVES rows (one-line reasons + what I tried)

- **A1-02** (register #1 residue (ii), `Fair`) — **SURVIVES**. Verified
  in code: `ChoiceSite.backEdge` exists (`State.lean:212`) with the
  fairness-expressibility note in its policy docstring (:255–256), so
  the semantics-side obligation (a fair scheduler is EXPRESSIBLE) is
  discharged by the site. Attacked the too-wide direction as well: the
  model's always-unfair streams are *permitted* — mem#badsync's "The
  loop in main is not guaranteed to finish" is the anchor — so
  `modeled ⊆ permitted` holds and nothing about the residue threatens
  either bound. The dangling `Fair` pointer is correctly deferred to
  A1-46; note the code itself is honest ("a **future** `Fair : Choices
  → Prop`") — only D:110's prose reads as if it exists.

- **A1-22** (E11, runtime-check order rides R9) — **SURVIVES**. The
  coupling argument holds under attack: I hunted for a check-order
  observable that is *not* message text — a case where order selects a
  different panic **class** (recoverable vs fatal, `runtime.Error` box
  vs plain-string box) rather than a different string — and found none;
  every within-one-operation check raises a `runtime.Error`, so order
  is visible only through text, which R9 pins. Site record verified:
  `Ops.lean:212`, "the runtime's exact messages and check ORDER
  (oracle-pinned 2026-07-25)". Widening order without widening messages
  really is incoherent.

- **A1-25** (R2, append spill declared pragmatic subset) — **SURVIVES**.
  I probed the envelope's containment argument on paper and could not
  escape it: gc's `roundupsize` is a size-class rounding bounded well
  under 2× for every regime (small size classes ~12.5% apart, large
  page-rounded), and `max(32, 2·growth)` covers the small-slice
  size-class floor (a 1-byte element append to nil lands at cap 8 ≤
  32). Recorded residual, not a weakening: the row's "modeled ⊊
  permitted is irreducible" is irreducible for the **executable**
  machine only — the Prop-level relation could carry the unbounded
  "any capacity ≥ newLen" envelope directly. Worth one sentence when
  the relation's extraction slice lands; it changes no disposition
  today.

- **A1-30** (R7, NaN payload narrowing) — **SURVIVES**, and its scope
  condition is verified rather than assumed. I checked that the
  escape channel is actually closed: `math` is **not** on the stdlib
  shim allowlist (`grep` over `stdlibshim.go` for math/`Float64bits`/
  `Signbit`: empty), so `math.Float64bits` cannot reach the machine.
  I then hunted for an in-language payload observable without math —
  `fmt` (`%v`/`%x`/`%s` all render "NaN"), float32 round-trips, NaN
  map keys (distinct by `valueEq`, payload-independent), sign — and
  found none. The row's honesty apparatus (recording it as a FIRST
  classification with the two rejected readings, and refusing (q)
  because no theorem exists) is the standard the rest of the corpus
  should meet.

- **A1-32** (R9, panic values/messages pinned to gc) — **SURVIVES**.
  Load-bearing and correctly priced: the strict equality lane exists
  because of this pin, and message envelopes would dissolve the
  differential's decisive signal for zero fidelity gain. I checked the
  A1-21 attack against it and it does not land the same way: the R9
  sites do carry a pin marker ("oracle-pinned", `Ops.lean:212/233/249`),
  unlike R1's bare `.int => some 64` and unlike E10's silent
  `entries.set!`. **Recorded residual** (not enough to weaken): the
  sites say "oracle-pinned" but not "no claim about message *content*
  transfers beyond gc"; that transfer sentence lives only in L:1046 and
  §8 e8. Fold it into the A1-21/A1-24 site-caveat sweep.

- **A1-33** (R10, abort-line rendering) — **SURVIVES**. Verified the
  fail-closed shape: `renderPanicPayload`/`renderPanicHead`
  (`Machine.lean:1547/1590`) return `Option String`, so the unmodelable
  edges refuse rather than guess. Crucially, this **insulates** the row
  from A1-09: the allocation-identity dependency is discharged by a
  refusal, not by a claim, so R10 does not inherit the orphaned
  quotient's problems. Riding R9's transfer caveat class (§8 e8) covers
  the "gc's stderr rendering is not portable" exposure.

- **A1-34** (R11 + R12, sync-misuse fatal class and exit codes) —
  **SURVIVES**. Verified R12's premise directly: exit codes appear in
  `GoLean/` **only inside docstrings** (`Multi.lean:343`,
  `Value.lean:170/187/194`) and never as machine content — so "harness-
  side keys, not machine content" is correct. R11's pin is a genuine
  two-member envelope {recoverable panic, unrecoverable fatal} that is
  control-flow observable, but it is pinned to the sole oracle at the
  pinned language version with version-tracking cases. **Recorded
  coherence note**: the row names ARCH ("pre-1.8 realizations
  differed") as the evidence class that would size the envelope, but
  the doctrine's own language-version pin (D:56–64, "GoCore models the
  Go 1.26 language") **excludes** pre-1.8 gc from bearing on the Go-1.26
  envelope. The version pin rescues the disposition and simultaneously
  kills the sizing route the row points at; the honest statement is
  "pinned at gc's Go-1.26 point, DOCS-underdetermined, no live sizing
  route."

- **A1-38** (U-2, L4 ⊆ L1-reachability) — **SURVIVES**. I attacked the
  "neither bound is at risk" claim from the upper-bound side and it
  holds: C5's `modeled ⊆ permitted` rests on spec **silence** about
  which waiter corresponds (mem#chan matches a send to "the
  corresponding receive" with zero text on which), so it is independent
  of whether L4 members are also L1-reachable. Either answer to U-2
  leaves both bounds where they are; it decides only whether the L4
  site is load-bearing or redundant machinery — a cost question.
  **Recorded nit**: "per-shape membership polices it where it matters"
  mis-describes membership, which polices too-*narrow*, not the
  redundancy question U-2 asks. Harmless.

- **A1-40** (U-6, future atomics) — **SURVIVES**, and the deferral is
  now verified guarded rather than assumed. Probe
  (`artifacts/p2probe/at5/`): a subject calling `atomic.AddInt64` is
  refused by the frontend with a named cause —
  `"package-selector call atomic.AddInt64 (package \"sync/atomic\"
  surface not modeled)"`. So "not modeled, deferred to the atomics arc"
  is true *and* fail-closed; there is no silent lowering of atomics to
  plain accesses. mem#atomic's SC pin is verbatim-anchored and forced
  when modeled; the residual (surrounding plain accesses) is correctly
  that arc's problem.

---

## Findings for lanes beyond A1

Recorded because they were produced by this pass and belong to other
lanes' objects:

1. **The site-caveat sweep is a grep and has never been run** (A1-21,
   A1-24, A1-32, A1-31). Three different rows in the census assert or
   assume a site-level record; one of them (E10) is provably false, one
   (R1) is a known two-week-old violation, two (R9, R8) are partial.
   The singleton-narrowing rule is enforceable mechanically over the
   (b)/(b-n) rows and is not enforced at all. → lane D (apparatus).
2. **`FloatBits.lean`'s envelope-statement block is the template** the
   other pins should be fixed against — narrowing declared, platform
   scoped, transfer sentence explicit, tripwire named. It is the only
   site I found that does all four.
3. **The frontend's fail-closed boundary held under every probe I
   threw at it** (atomics, unsafe, `%p`, float→int). The one recorded
   fail-open in that area is pre-existing and self-documented: dot
   imports (`import . "strings"; Fields(x)`) reach `stuck`, not a
   boundary refusal (`stdlibshim.go:31–43`). Visible red, but the wrong
   kind. → lane A3.
4. **`go run <files>` vs `go run .` is a general oracle-scope fact**,
   not only E8's problem: the harness invokes the oracle in directory
   mode (`scripts/diff-coverage:832`), so every claim of the form
   "observed ⊆ modeled" is scoped to directory-mode builds. That scope
   is nowhere stated. → lane B (lower bound) / A1-05's oracle matrix.
