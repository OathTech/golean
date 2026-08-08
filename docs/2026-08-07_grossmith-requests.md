# GoLean → grossmith: prioritized generation requests (2026-08-07)

(Committed to docs/ 2026-08-07, verbatim from the working-note
.tmp/grossmith-requests-2026-08-07.md — this provenance paragraph is
the only addition; the campaign record it cites at a .tmp path is
committed as docs/2026-08-07_grossmith-campaign.md.)

From the GoLean project, following the 2026-08-07 campaign (grossmith
5b4c5b0 vs GoLean 458386d: 2,900 cases, zero divergences, harness
contract verified — see `.tmp/grossmith-campaign-2026-08-07.md` /
`docs/2026-08-07_grossmith-findings.md` addendum). Scope: hardening the
SEQUENTIAL semantics; concurrency is explicitly out (on both roadmaps).

Method note: every request below is grounded in GoLean's own defect
ledger (`docs/BUGS.md`, 43 entries) — "what generation would have found
mechanically the bugs our adversarial audits found by hand." Priority
order is by demonstrated yield, not speculation. Minimal repro shapes
cite the corpus cases that now pin each class (all under
`Corpus/coverage/exec/`, canonical Go, freely reusable as grammar
seeds).

## R1 — A recover-based observation idiom (highest yield)

Your profile excludes defer/recover as observation-event-shaped. Our
ledger says that exclusion costs the single largest observable class:
the assignment phase-ordering family (BUG-022/025/029/030/033), panic
identity (which panic fires first), and store-before-panic partial
state are observable ONLY through a recovered panic plus surviving
state. Ask: ONE canonical wrapper shape —

    func fuzzSubject() int {
        r := 0
        defer func() { if p := recover(); p != nil { r = <encode(p)> } }()
        <generated body writing observable locals>
        return <encode(state)>   // or r via named result
    }

— deterministic, strict-lane, no new observation kinds (the panic
value/message encodes to int by table). Seed shapes:
`multi-assign/store-order-plain`, `channels/recv-edge` (sequential
halves), `multi-assign/field-nil-store-time`.

## R2 — Multi-target assignment + order-witnessing grammar

The most bug-dense corner of the project (8+ ledger entries), currently
grammar-blocked on your side. Wanted: aliased targets (`i, a[i] = …`),
nested address chains (`a[i].f`, chains through pointers), comma-ok
forms (map/assert), tuple returns into mixed targets; and generally
ORDER-WITNESSING generation — every subexpression bumps a counter via a
call, the returned value encodes the realized order. This mechanizes
the evaluation-order class (BUG-023/026/032, short-circuit operands).
Seed shapes: `multi-assign/chain-field-over-index`,
`multi-assign/comma-ok-forms`, `channels/recv-order` (sequential
shapes), `assign-order/target-check-vs-rhs`.

## R3 — Kind/definedness matrix sweeps

We found three sites of one synthetic-literal kind-defaulting family
SERIALLY (BUG-042 incdec → map-compound → BUG-043 range-over-int; your
seed 559 started it). The lesson: sweep the full matrix wherever a
literal or default kind can enter — {every arithmetic/compound/incdec/
range/index site} × {int8..uint64, float32/64} × {defined vs unnamed},
with in-kind arithmetic on the results (conversion-free — `int(x)`
laundering masks the class; see `range/int-kind-arith` vs the older
`range/range-int-typed`). Small grammar, exhaustive value.

## R4 — Construct-PAIR interaction coverage as a swarm objective

Our worst cross-cutting findings were all pair interactions no
single-feature corpus exercises: promotion wrappers × recover
(BUG-015), goto × package globals, generics × function-local types
(BUG-018), aliases × interface dispatch, defer × quarantined builtins.
You have swarm infrastructure; ask: pairwise feature co-occurrence as a
coverage target (generate n cases per feature PAIR, not per feature).
This is the systematic form of what our adversarial audits do manually,
and it scales where reviewer wit does not.

## R5 — Maps/slices into observed positions via canonical aggregates

Currently masked out of observed positions for order reasons. Cheap
unlock: order-independent observables — sorted-insertion sums, length +
membership-bit encodings, min/max folds — keep strict-lane determinism
while exercising map/slice machinery hard (append/growth, delete,
aliasing, nil semantics). Later, optional: emitting `membership`-lane
rows with `width` metadata per our lane spec
(`docs/2026-08-04_membership-lane-design.md`) — but aggregates get most
of the value with zero harness change.

## R6 — Embedding/promotion/interface matrices

Bounded grammar, enumeration-friendly, slice-2's whole bug field:
{value/pointer/interface embedding, 1–3 levels} × {value/pointer
receivers} × {static call, interface dispatch, method value, method
expression} × {nil/non-nil at each hop} × {typed-nil in interface}.
Seed shapes: `embedding/value-embedded-pointer-promotion`,
`interfaces/recover-promoted-wrapper` (pairs with R1),
`methods/alias-promoted-method-expression`.

## Non-asks (deliberate)

- Concurrency — our enumerator/lane machinery covers it ahead of what
  generation could check; revisit when both roadmaps are ready.
- goto/labels — rare idiom, envelope pinned, low expected yield.
- Float bit-exactness beyond int-conversion observables — needs our
  observation format; int-encoded comparisons already reach most of it.
- Anything requiring go.mod/module mode — the harness is GOPATH-mode;
  also note your witness suite is red in stock module mode (bare
  t.TempDir(), no go.mod) — your issue tracker probably knows.

If only two land: R1 + R2 together would have mechanically found most
of what our hardest audit rounds found manually. All six compose: R1's
wrapper is the observation channel R2/R4/R6 want.

---

## Addendum (2026-08-08): outbound items from the external Codex semantic-divergence review

Source: `docs/2026-08-08_semantic-divergence-review.md` (external Codex
review, read-only, GoLean 06933964 / grossmith a09bf911, Go 1.26.5),
§4–§5. Its campaign: 250 cases, seeds 2000000..2000249, 225 semantic
matches, 0 mismatches, 25 clone-infrastructure failures. Two asks for
grossmith and one reporting convention, recorded here as the outbound
channel; full detail in the review doc.

### G1 — recover-wrapper caught-panic observation is profile-incompatible with the GoLean clone (R1 is blocked)

The highest-yield surface we requested (R1 above) is currently
ineffective: `fuzzPanicCode` (grossmith `gen/gen.go:1171-1176`) attempts
`p.(error)` and then calls `e.Error()` on the recovered value, and the
GoLean clone does not support the `$runtime.Error` method set — so in
the review's campaign every wrapper that actually caught a runtime
panic became a clone-infrastructure failure ("wrapper-caught: 19;
successfully compared caught-panic executions: 0"). The 40 generated
`recover_wrapper` cases therefore do not mean 40 recovered-panic
behaviors were validated: green wrappers were no-panic paths. The
review's three candidate directions, quoted:

> - avoid method dispatch on recovered runtime errors in the GoLean
>   profile;
> - encode known runtime panic classes through an observation mechanism
>   already supported by the clone;
> - or treat `$runtime.Error` support as an explicit prerequisite and
>   label the recover rung unavailable until it lands.

And the constraint, quoted: "The replacement must still distinguish
which panic occurred. Merely recording that some panic was recovered
would lose the ordering discrimination R1 was designed to provide."

(GoLean-side note: the `$runtime.Error` method-set gap is also OURS to
consider — whether the machine should support `Error()` on recovered
runtime errors is parked in `TODO.md` (2026-08-08 entry, not
implemented); a resolution there would satisfy the third direction.)

### G2 — harden reference builds against Go 1.26.5 VCS stamping

Stock-environment `go test ./...` and generated reference builds fail
with "error obtaining VCS status: exit status 128 / Use -buildvcs=false
to disable VCS stamping"; `GcAdapter`'s sanitized environment
(`harness/harness.go:252-273`) drops an external
`GOFLAGS=-buildvcs=false`, leaving no ordinary campaign CLI route to
the workaround (the review used a scratch-only `go env -w`). Ask: make
the reference build independent of ambient VCS stamping — add
`-buildvcs=false` to the build invocation or support a deliberate
build-flags/environment path — plus a stock-environment test for it.

### G3 — campaign reporting: judged vs generated counts

Per the review §5 G3 (and §4's lesson): campaign reports should state,
per high-value feature rung, BOTH the gross generated count and the
successfully judged (actually compared) count, so profile
incompatibilities cannot look like tested semantic coverage — this
campaign's recover rung read as "40 recover_wrapper cases" while the
judged caught-panic count was 0.
