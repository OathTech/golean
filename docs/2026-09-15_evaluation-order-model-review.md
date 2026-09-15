# Review of the evaluation-order design at `90dc66f0`

[AGENT] Review and proposed corrections, 2026-09-15, requested directly by
[USER]. Reviewed artifact: `90dc66f0:docs/2026-09-15_evaluation-order-model.md`
and that commit's `docs/evidence/2026-09-15_eval-order-model-spike/`.
Implementation references below are at its base, `a7d553f7`. Review branch:
`review/eval-order-model-0915`, branched from that main tip. This companion
does not amend the design, authorize implementation, or resolve its user gates.

## Verdict

**Revise before implementing the proposed general envelope.** The dependency
relation is the right direction, and successful early values must be preserved
to address BUG-101. However, the proposed lowering does not yet implement the
relation in §1. It misses legal placements and failure outcomes; its
compound-assignment sketch can combine an early value with a different store
target. Binder lifetime and the extension to intermediate positions are also
underspecified in ways that can change results.

The static census reproduces exactly on the retained wires. Its interpretation
as a bound on pairs, evaluations, or tape consumption does not follow.
BUG-101/104 should be described as **intended applications, with correctness
still to establish**, rather than resolved by this design.

All findings and corrections below are [AGENT] proposals. The priorities concern
the design as written; these are not claims that an unimplemented `unseqUse`
already causes production failures.

## Findings and proposed corrections

### F1 — High: lexical/residual placement omits positions before earlier calls

**Where:** §1 U1/U3; §2 wire, lines 75–84; §5 item 3.

The relation leaves a sensitive operand unordered against a sibling event on
either side. The wire instead pairs operands only when something eligible
follows them, and places the first probe at the operand's lexical position.

```go
a := 1
mut := func() int { a = 2; return 0 }
v := mut() + a
```

Under §1, reading `a` before or after `mut` gives `v` in `{1, 2}`. The proposed
wire has no probe for `a`: there is no later event. It produces only `2`.
Re-emitting probes after subsequent events does not add the missing earlier
position. The same issue occurs within `sink(mut(), a)`; the outer call forces
both arguments before entry, but does not order this read after `mut`.
This is an inference from the pinned ordering clause and the repo's I-2
interpretation, not a claim that gc exhibited `1` in this probe.

**Correction:** compute an operand occurrence's legal positions from its
dependencies and enclosing control region. Permit positions before lexically
earlier sibling events when no dependency forbids them. The lower bound on
placement is dependency readiness, not source position. If an initial slice
retains the narrower scheme, state that restriction and keep its affected
inventory rows narrowed; do not mark E2/E12/E14 generally enveloped.

**Required check:** place the mutable operand on both sides of the call, both
as arithmetic operands and as arguments of an enclosing call. Retain a control
where the operand actually needs that call's result.

Ground: spec#Order_of_evaluation and spec#Calls at the pinned source; the
[ordering section](https://github.com/golang/go/blob/c19862e5f8415b4f24b189d065ed739517c548ba/doc/go_spec.html#L5836),
and [I-2](spec-interpretations.md#i-2-not-specified-evaluation-order-is-unsequenced-not-either-order--backed-by-l-013).

### F2 — High: retaining today's whole-operand probes loses subexpression interleavings

**Where:** §1 F4/U2/U3; §2's binders on today's probes; §6 slices 1–2.

Today's emitter subsumes a child's probe into its parent
(`tools/nativefrontend/emit.go:5288`, `:5448`; e13-b design §4 D1).
That is insufficient for the new value relation:

```go
a := []int{10, 20}
b := []int{0}
mut := func() int { a[0] = 30; a[1] = 40; b[0] = 1; return 0 }
v := a[b[0]] + mut()
```

An early evaluation of the whole `a[b[0]]` returns `10`; a late one returns
`40`. But `b[0]` can produce `0`, then `mut` can run, then the outer read can
produce `30`. That order satisfies the child's dependency on the outer
operation and the stated U1 latitude. A probe/use pair for the whole expression
only offers `{10, 40}`. There is just one mutating event here: adding positions
between multiple events does not fix this case.

**Correction:** define nodes as evaluation occurrences with explicit produced
values and dependency edges. A parent consumes its children's selected values;
it must not replace their independent legal placements by reevaluating the
entire source subtree at one endpoint. Restrict U2 to independent occurrences:
an operand and its parent are not an unordered pair. Any optimization that
subsumes a child's probe needs an outcome-preservation condition.

Also derive sensitivity from the reads performed by an operation, not just
visible identifier/index syntax. For example, `string(b)` for a byte slice
reads its backing data; caching only `b`'s unchanged descriptor does not cache
the converted string. The implementation's `.stringFromByteSlice` reads those
elements in `GoLean/GoCore/Machine.lean:376`. Include byte/rune conversion and
aggregate-copy cases when defining P and allocation-payload capture.

**Required check:** the nested example's reference set is `{10, 30, 40}`.
Validate shared child values across the parent operation, including when one
candidate child evaluation fails.

### F3 — High: compound assignments must share target identity, not just a read value

**Where:** §2 LATE once-temps; §3 BUG-104, lines 135–149.

The sketch stores into `x[$c1]` after using a separately captured early read of
`x[$c1]`. The shown `fnine()` case has a stable target, so it cannot test whether
the read and write refer to the same element when the RHS mutates the target
operands.

```go
a := []int{10, 20}
i := 0
mut := func() int { i = 1; return 1 }
a[i] += mut()
```

Capturing the early read `10` and recomputing the target late as `a[1]` gives
`[10, 11]`. This violates the once-evaluated LHS requirement. Evaluating the
target early permits `[11, 20]`; evaluating it late permits `[10, 21]`.
The hybrid `[10, 11]` is not licensed. Even the sketch's call-containing
shape has the problem if `wit` reassigns the slice variable `x` while the
returned index stays fixed.

The map spelling's shared key temp is useful, but it must also share the
selected map identity. Moving its base/key binding late without capturing
their earlier alternatives simply replaces one position pin with another.

**Correction:** represent the selected target operands/identity once and use
that same target for the read and store. Give the value read its own permitted
timing where necessary; coupling target identity does not justify moving all
reads or all checks to phase 2. Preserve the distinction between phase-1
operand failures and the store's check. Explain how an early read's target
choice is retained through the RHS call.

**Required checks:** mutate the index, replace the slice/map base, redirect a
pointer, and mutate the selected cell without changing its address. Assert
absence of hybrid read/store results as well as presence of the valid members.
The existing emitter comment already identifies the once-evaluation obligation
at `tools/nativefrontend/emit.go:4671`; spec#Assignment_statements is the rule.

### F4 — High: the stated no-event scheme cannot produce the last operand's panic

**Where:** §2 pair eligibility; §5 item 4; §6 slice 2's E3/E4 retirement.

```go
var a, b []int
_ = a[1] + b[2]
```

U2 permits either independent bounds failure to be first. The stated rule
pairs `a[1]` because a sensitive operand follows it, but does not pair
`b[2]`. RAISE produces the `a[1]` failure at the probe. DEFER reaches the
residual's left operand and produces that same failure. `b[2]` never runs.
Consequently the stated scheme produces one panic identity, not both.

**Correction:** schedule all eligible independent failure nodes, or specify a
probe construction that can actually execute the last one ahead of the first
residual failure. Check completeness against their dependency graph; the
phrase “DEFER×RAISE gives the permutations” is not a construction. Keep E3/E4
open until this no-event family is covered.

**Required checks:** two and three independent panics without calls, each
position as the only failing operand, and nested dependent failures as controls.
If the existing `unseqPanic` bound remains 2, it pops even when only one
operand fails. The “pops only when ≥ 2 fail” claim also needs correction.

### F5 — High: binders need a fresh dynamic lifetime and a reset on deferred failure

**Where:** §2 wire/decoder/machine, lines 75–98.

A VALUE writes `$uN` into the frame environment; a PANIC uses the unchanged
DEFER/RAISE rule. No reset is specified. One static pair can execute repeatedly
inside a loop, so static pairing alone does not establish that a stored value
belongs to this evaluation of the sweep.

```go
a := []int{7}
mut := func() int { a = nil; return 0 }
for j := 0; j < 2; j++ {
    println(a[0] + mut())
}
```

On the proposed early-success path, the first iteration can bind and return
`7` despite the late panic. The second iteration starts with `a` nil. If its
probe defers without clearing the binder, the late panic can again choose the
previous iteration's `7`. That successful second iteration has no source
evaluation order: `a[0]` fails throughout it.

**Correction:** give saved outcomes a per-dynamic-sweep lifetime. Reset a slot
before every probe attempt, including the panic/defer path, or allocate a
fresh region of slots each time the sweep runs. Specify disposal at normal and
exceptional exits, branch dominance of uses, and isolation across calls.
An absent slot must mean “no successful candidate in this sweep,” never “reuse
whatever the previous execution left behind.” Require type and expression
agreement for a pair, in addition to name matching and uniqueness.

**Required check:** a loop whose first early evaluation succeeds and whose next
iteration's early and late evaluations both fail. Also cover conditional entry
and recursion. This finding is an omitted invariant in the design, not a
measurement of implemented binder behavior.

### F6 — High: re-emitting a two-slot probe does not implement all intermediate positions

**Where:** §5 item 3 and §6 slice 4.

Suppose one read could see `0`, `1`, and `2` before, between, and after two
ordered mutations. A single saved `w` plus a late `v` offers at most two
successful alternatives at its use. Re-emitting the same binder after each
event overwrites `0` with `1`, leaving `{1, 2}`. Giving the probes distinct
names does not help unless the use can select among all their saved values.
It also changes the decoder's stated one-bind/one-use discipline.

**Correction:** specify either a scheduler that chooses one ready evaluation
position and evaluates the occurrence once, or a candidate collection with a
defined multiway selection protocol. Include intermediate failures, failed
events, scope resets, dependencies, and early termination in that protocol.
A binary choice tree is possible, but its worst-case pop count grows; one
multiway pick changes the bound. “Pops unchanged” is not established by the
present two-slot table.

This remains a user-gated extension. Accepting the endpoint slice would not
validate this later extension or the complete relation automatically.

### F7 — Medium: structural difference does not establish observability or tape stability

**Where:** §2 lines 99–105; §5 items 1/4; §6 cost claims.

`BEq GoValue` is structural equality (`GoLean/GoCore/Value.lean:962` onward).
Different values need not produce distinguishable observations. For example,
`_ = a + mut()` can have different early/late values of `a` even though both
paths discard the result and have the same event effects.

Further, a new `unseqValue` pick consumes a tape element whenever its bound
is 2. That changes which element reaches a later choice site in the same
execution. Canonical slot 0 does not prevent this. The unchanged `unseqPanic`
site always consumes at a failing probe, including when both positions have
the same eventual failure and effect prefix.

**Correction:** describe this as **consult on structural value difference**,
a proposed reduction in redundant picks. Distinguish:

- equality of outcome sets over all tapes;
- behavior under the canonical/empty tape;
- preservation of a particular nonempty tape and its consumption trace;
- actual observational equivalence of two candidates.

Only the first is an envelope claim. State the required assumptions and proof
obligation for delaying a successful candidate's choice until its use. Include
dependency/target consistency and branches that never reach the use. Restrict
the “unchanged” claim to cases that add no effective consult, and measure the
other cases. A new late default also changes previously early once-temps, so
“slot 0 byte-identical to today” is too broad for the whole proposed slice.

### F8 — Medium: the census is reproducible, but its counts are not upper bounds

**Where:** §6 lines 201–211; spike README and `count.py`.

Re-running the tracked script against the retained 1,330 corpus wires and the
twin wire reproduces every row of `counts.tsv`, including 118/128 probes and
383/277 panicky residual nodes. This is a successful reproduction of the
static counting calculation, not a fresh lowering or differential run.

The script cannot justify the stronger interpretation:

- `sweeps` examines operand nodes only in the closing residual statement.
  It skips the expressions in accumulated call/temporary/allocation hoists.
  An unordered operand before an inner call in an outer call's argument list
  can be inside such a hoist, rather than the closing residual.
- Only event-bearing sweeps contribute candidate nodes. The proposed U2
  pairs in no-event sweeps are omitted entirely.
- The panicky census omits signed shifts, interface comparisons, and
  slice-to-array conversions listed in P(i). Including extra private-local
  reads elsewhere does not prove that these omissions are covered numerically.
- A static occurrence can execute arbitrarily often in a loop or recursion.
  Approximately 1,400 static pairs cannot bound dynamic extra evaluations or
  pops. Whole-expression duplication also costs more than one primitive read.
- The reproduction loop discards lowering errors and continues; `count.py`
  likewise skips unreadable JSON and exits successfully. The number 23 alone
  does not establish that every missing directory is a designed refusal.

**Correction:** relabel the current numbers as a residual-node census over
successfully retained inputs. To claim an upper bound, account for every
eligible location and kind, explain nesting/subsumption, and keep static
occurrences separate from dynamic visits and costs. Save a small input/refusal
manifest with causes; make the census fail on missing or malformed expected
inputs. A cost experiment should report visits, picks by site/bound, fuel,
time, and memory for fixed workloads. Do not turn the “~30 known” fixture
list into a pop bound.

### F9 — Medium: complete the semantic contract and preserve the accepted validation debt

**Where:** §1 objects/F1/F6/Outcome; §4; §6–7 and Handoff.

The following corrections make the proposed relation and its validation
reviewable independently of the probe implementation:

1. Define event occurrences and nesting precisely. A literal source-position
   comparison orders `f` before `g` in `f(g())`, while F2 requires the opposite.
   Specify argument evaluation before invocation and lexical order among
   independent event occurrences. Make conditional regions explicit so an
   unexecuted short-circuit RHS contributes no evaluated nodes.
2. Include produced values and resulting state in the sweep result, with an
   explicit observation projection. The current “effect prefix and first
   failure” summary does not state how normal returned values are compared.
   Explain failure propagation/recovery and the sequential terminating domain
   of the prototype; receives can block and calls need not return.
3. Qualify F6's range rule with its constant-expression exception
   (spec#For_statements). Do not generate evaluations for unevaluated constant
   `len`/`cap` operands (spec#Length_and_capacity). Make the built-in list either
   exhaustive for the admitted fragment or explicitly scoped; specify the
   treatment of statement-only built-ins and other nonconstant built-ins.
4. Derive the reference enumerator from the source dependency graph. It should
   enumerate legal executions and first failures, not reproduce the proposed
   DEFER/RAISE construction and compare that construction to itself. Add
   forced negative controls as well as membership witnesses.
5. F2/F3 constrain particular dependencies, not every expression inside a call
   or logical RHS. `sink(a, mut())` still has unordered argument work; an
   evaluated RHS may contain such work too. Only controls deliberately having
   no remaining unordered choices can be asserted singleton. Likewise, a
   compiler can select different allowed branches across runs: a fixed draw
   in these probes is an observation, not a general “gc draws ONE” guarantee.
6. Keep the small translation certificate visibly owed. The accepted F6 row
   in [the master plan](2026-09-05_master-plan.md) §7.2 includes it. Exact
   enumeration of finitely many generated fixtures is useful testing but
   does not discharge that obligation. Assign a bounded fragment and an exit
   criterion, or propose an explicit plan change; “No translation certificate”
   should not silently remove it. It need not exist to finish this review.

## Suggested revision sequence

1. Rewrite §1 as a dependency graph over evaluation occurrences and guarded
   regions, with explicit value/state results. Resolve F1–F3 in that graph.
2. Build the bounded reference model first. Include the witnesses above,
   multiple failures, assignment phases, short circuiting and a buffered
   receive. Keep oracle membership and model completeness as separate checks.
3. Specify the implementation mapping, binder lifetime, shared target identity,
   candidate multiplicity, and tape contract. Prove or test each claimed
   optimization against the reference before using it to retire latitude pins.
4. Recount candidate sites and measure dynamic costs using that mapping. Then
   revise slice scope and estimates, preserve the translation-certificate
   obligation, and re-pose the existing user decisions against the corrected
   design. Do not infer a ruling from this review.

## Validation record and limits

[AGENT] Read the pinned Go source at
`c19862e5f8415b4f24b189d065ed739517c548ba` (`deps/go`, verified HEAD), the
design at `90dc66f0`, its census script/README, the existing probe implementation
and emitter, the E13 design, I-2, and the accepted F6 requirements. The public
pinned spec link above was also checked. These are design-level findings;
no new interpreter or frontend implementation was tested.

**Go smoke probes:** the F1/F2/F3/F4/F5 snippets were wrapped in function-local
blocks, printed where appropriate, and given a deferred recovery printer for
the panic cases. Toolchain: `go version go1.26.5 linux/amd64`, matching
`baselines/go-oracle-pin`. Both commands exited 0 with the same output:

```sh
GO111MODULE=off GOCACHE="$PWD/artifacts/go-build-cache" go run "$probe_dir/probes.go"
GO111MODULE=off GOCACHE="$PWD/artifacts/go-build-cache" go run -gcflags='-N -l' "$probe_dir/probes.go"
```

```text
right-read 2
compound 10 21
nested 40
two-panic runtime error: index out of range [1] with length 0
loop-event
loop-panic runtime error: index out of range [0] with length 0
```

The loop's gc run fails in its first iteration; the stale-binder witness
instead follows the new design's proposed early-success member before entering
its second iteration. These smoke runs establish compilability and these gc
draws only. The other members and forbidden hybrids above come from the stated
dependency/once-evaluation arguments.

**Census reproduction:** from the design worktree, ran:

```sh
python3 docs/evidence/2026-09-15_eval-order-model-spike/count.py baselines/pins/twin-chdriver.wire.json
python3 docs/evidence/2026-09-15_eval-order-model-spike/count.py .tmp/wires/*.json
```

Both exited 0 and matched all tracked metrics. The wires were reused; the
1,353-directory lowering sweep and the classification of its 23 refusals were
not re-certified. Two direct in-memory calls to the script's `sweeps` function
also confirmed its exclusions: a no-event residual with two indexes contributes
no candidate count, and a call hoist carrying an index argument followed by a
temp-only return reports zero panicky residual nodes. These are scope checks
on the counter, not estimates of the corrected model's eligible-pair count.

A small scratch enumeration of the three nodes `inner-read`, `mut`,
`outer-read`, with `inner-read < outer-read`, produced `{10, 30, 40}` for F2;
the two whole-expression endpoints produce `{10, 40}`. No generated corpus,
Lean build, full CI run, or differential re-certification was performed for
this records-only review. Runtime code, baselines and the reviewed note remain
unchanged.

**Records checks:** `git diff --cached --check`, `scripts/check-agents-alias`,
`scripts/check-evidence-size`, and `scripts/check-spec-anchors` passed. The
anchor checker resolved 838 spec, 255 memory-model and 26 library citations at
the pin; its existing `docs/BUGS.md` binary-file diagnostic was visible. Local
Markdown link targets and code-fence balance were also checked. These focused
checks are not a full CI or merge-certification claim.
