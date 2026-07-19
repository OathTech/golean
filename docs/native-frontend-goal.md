# Native Go Frontend — Operating Guide

Authoritative guide for building the native Go frontend. An agent should be
able to read this with no conversation context and know the target, the
contract, the scope, and how to validate. Companion to
`docs/gocore-semantics-upgrade-goal.md`; the same discipline applies
(`CLAUDE.md` validation gate, fail-closed, small slices, honest regressions).

## Why

Gobra is the throughput and coverage bottleneck: only ~136 of 672 corpus cases
reach Lean, Gobra rejects legal Go (`delete`, `string(65)`, `fallthrough`,
some map-range), exports per-fixture via SBT, and the harness is
one-file-per-package. The north star (`etcd-io/raft`) is multi-package modern
Go that Gobra cannot handle. See `docs/2026-07-18_prioritization.md`: the
native frontend is both the biggest throughput lever and the largest
design-debt retirement (it also retires the adjacency-based type recovery).

## The contract: a clean native wire + a native lowering adapter

Decided 2026-07-18 (superseding the earlier "reuse the Gobra wire" note). The
invariant is **GoCore is untouched**, not "reuse the Gobra wire". Emitting the
Gobra schema from `go/types` would mean synthesizing Gobra-shaped baggage
(Source origins, addressability, desugaring patterns) and satisfying
`GobraToIR`'s recovery heuristics (adjacency type reconstruction, desugared
multi-assign/call-assign matching, return postprocessing, proxy-name
stripping) — coupling the native frontend to the very quirks we are escaping,
even though `go/types` has already resolved everything cleanly.

Instead:

- The native frontend is a Go program using **`go/parser` + `go/ast` +
  `go/types`** (stdlib; the coverage harness already uses the parser half).
  `go/types` hands back fully resolved types, defined types, folded constants,
  and — importantly — **method sets and interface type-sets**, the metadata
  that was frontend-gating Phase 5 interfaces.
- It emits a **clean native wire schema** shaped by `go/types` (a new
  `GoLean/NativeJson.lean` decoder), lowered by a new **`GoLean/NativeToIR.lean`
  adapter** into the same fixed GoCore — parallel to `GobraJson`/`GobraToIR`,
  not replacing GoCore. Because `go/types` resolved names and types up front,
  the lowering is direct with no recovery heuristics.
- Dependencies: **stdlib only**. `go/importer` resolves stdlib imports
  (`math`, `strconv`); no `golang.org/x/tools`. Multi-package loading can add
  `go/packages` later if source-level cross-package loading is needed.
- Fail closed: an unrepresentable construct is an explicit adapter error, never
  an approximation.

Location: `tools/nativefrontend/` (Go, `GO111MODULE=off`, stdlib only). Harness
selects it via `GOLEAN_FRONTEND=native` (switch already exists in
`scripts/diff-coverage`; default stays `gobra` until parity).

## Endgame: eliminate Gobra entirely

The success criterion is not "runs quorum" — it is **the native frontend covers
what Gobra covered so Gobra can be deleted**. Gobra was always a temporary
frontend accelerator (roadmap, AGENTS.md); GoCore is Gobra-free, the corpus is
frontend-independent, and proof infra is planned on top of GoCore, not via
Gobra. Removing it drops ~780 MB of Scala/SBT/JVM dependencies plus four Lean
modules, scripts, and CLI surface, and it deletes the per-fixture export
bottleneck.

Removal set (delete only after native reaches/exceeds parity and the default is
flipped): `third_party/gobra` submodule; `deps/gobra`, `deps/sbt-cache`,
`sbt-launch*.jar`; `GoLean/GobraJson.lean`, `GobraToIR.lean`, `GobraEval.lean`,
`Artifact/Gobra.lean`; `scripts/gobra-sbt`, `scripts/gobra-smoke` and the export
path in `diff-coverage`; the `gobra-*` CLI commands.

Sequencing: build native in parallel → reach parity on the corpus (start with
the 136 currently-validated cases, then the ~536 Gobra could never export,
then the 39-case quorum set) → flip `GOLEAN_FRONTEND` default to native →
verify no regression → delete Gobra.

## Validation strategy: parity on the corpus first, then quorum

Build and prove the exporter against the **existing 672-case corpus** (real Go,
known-good Go oracle) before pointing it at raft. This validates the exporter
against cases whose expected behavior we already know, and directly attacks the
536 stranded cases. Only once the native path is at/above Gobra parity on the
136 (and ideally reaching many of the other 536) do we run the quorum pilot.

Validation gate per slice (per `CLAUDE.md`): `lake build` is unaffected (no
Lean change expected); build the exporter; run `GOLEAN_FRONTEND=native
scripts/coverage run <slice>`; diff the failing-set against the Gobra baseline
for the same cases. Same-or-better = good.

## Stage-1 pilot target: quorum (`deps/raft/quorum`)

Feature census of `deps/raft/quorum` (done 2026-07-18):

**Verification-relevant core** — `MajorityConfig.VoteResult`,
`MajorityConfig.CommittedIndex`, and the `JointConfig` equivalents — uses only:
- defined types over primitives, maps, and arrays (`type Index uint64`,
  `type MajorityConfig map[uint64]struct{}`, `type JointConfig [2]MajorityConfig`);
- value-receiver methods on those defined types;
- maps: `range` and comma-ok lookup (`v, ok := votes[id]`);
- slices/arrays: `make([]uint64, 0, len(c))`, `append`, indexing, `srt[:n]`,
  `var stk [7]uint64`;
- `len`, uint64 arithmetic, comparisons, `if`/`for`/`continue`/`return`,
  block scopes;
- stdlib: `math.MaxUint64` (a constant) and `slices.Sort` (one extern).

**Not verification-relevant** — `String`, `Describe`, `voteresult_string.go`:
`fmt`/`strings`-heavy display code. Stub or defer; do not let it drive scope.

Key finding: the safety-relevant vote math is remarkably self-contained. GoCore
already executes almost all of its semantics (maps, slices, arrays, defined
types, uint64, control flow all have corpus coverage). The missing piece is the
*frontend*, plus a tiny extern surface (`math.MaxUint64`, `slices.Sort`).

## Sufficiency: green suite ⟹ quorum covered

The bar (set by the user): passing the differential suite should *necessarily
imply* quorum is covered. That needs three layers, strongest last.

### Layer 1 — isolated feature cases (localize failures)

Every Go construct quorum uses gets its own minimal corpus case, so a failure
points at one feature. Audit of `deps/raft/quorum` vs the existing corpus
(2026-07-18):

Already isolated (present, green or classified): comma-ok map lookup
(`maps/map-comma-ok`), map range (`range/range-map-sum` — note some map-range
cases are frontend json-check red today), `make([]T,0,cap)` (`builtins/make-slice`,
`slices/*`), typed iota (`constants/typed-iota`), defined int-type operators
(`ints/defined-type-ops`), uint arithmetic and division rounding (`ints/*`).

**Gaps — canonical Go + `cases.tsv`; frontend-blocked until the native
frontend lowers them, which is expected and correct — the corpus is
frontend-independent.** All quorum-relevant cases (isolated + integration) carry
the `quorum` tag, so `scripts/coverage run --tag quorum` runs the whole
sufficiency set. Status as of 2026-07-18:

1. [added] Defined map type `type M map[uint64]struct{}` + value-receiver method
   on it — `methods/defined-map-receiver` (a faithful `VoteResult` reduction;
   also the fix for "no method on any non-struct receiver existed corpus-wide",
   quorum's central idiom).
2. [added] Value-receiver method on a defined primitive type (`type Index
   uint64`) — `methods/defined-int-receiver`.
3. [added] Defined array type + method + indexing — `arrays/defined-array-receiver`.
4. [added] `map[K]struct{}` set idiom (empty-struct value, comma-ok membership)
   — `maps/set-membership`.
5. [added] Nested defined types (map value is a defined type `map[uint64]Index`)
   — `maps/defined-map-value`.
6. [added] On-stack-array-else-make + fill-from-right (the `CommittedIndex`
   slice trick, both branches) — `slices/array-to-slice-conditional`.
7. [pending] Fill-from-right → sort → index-median as the full `CommittedIndex`
   algorithm — depends on the `slices.Sort` extern; lands with slice 5 as a
   Layer-3 integration case.
8. [pending] Defined array type *over a defined type* (`type J [2]M`) — the
   `JointConfig` shape; add with slice 3.

### Layer 2 — edge enumeration (souped up)

Status 2026-07-18: the two safety-critical algorithm boundaries are covered.
- `quorum/vote-result` (7 subjects): empty-wins, won-exact, lost, pending,
  even-won, even-one-short, tie-lost — the tally decision boundary.
- `quorum/committed-index` (5 subjects): empty→MaxUint64, all-acked median,
  unacked-drags-median, on-stack (n=7), heap (n=8) — the slice/median boundary.
  Hand-rolled sort for now; a `slices.Sort`-faithful variant lands with that
  extern. **Watch item**: the empty case observes `MaxUint64`
  (18446744073709551615) — Go emits it cleanly; verify GoCore/observation-eq
  handle full-width uint64 when the native frontend first runs this case.

Both authored via the harness reflection observation (subjects return the
value; no `main`). Remaining Layer-2 families below are pending.

For each feature, cover the boundaries quorum actually hits, not just the happy
path:

- maps: empty, single key, many keys; comma-ok hit and miss; iteration is
  **order-insensitive in quorum** (every function counts or sorts), so the
  observations are deterministic and belong in the default lane even though raw
  map order is `deferred-nondet`.
- uint64: `math.MaxUint64`, wrap boundaries, `n/2 + 1` for even and odd `n`,
  `n == 0`.
- slice/array: `n = 0, 1, 7` (the on-stack boundary), `n = 8` (heap path);
  zero-fill-on-the-left semantics after filling from the right.
- vote tallies: all-yes, all-no, exact quorum, one short, missing voters, ties.

### Layer 3 — integration + input fuzzing (the sufficiency guarantee)

Bring `quorum`'s verification-relevant functions themselves into the corpus as
differential cases — `MajorityConfig.VoteResult`, `CommittedIndex`, and the
`JointConfig` variants — driven by a table of input vectors that exercise the
Layer-2 edges. Then **fuzz the inputs**: generate many small random configs and
vote/ack maps, run Go vs Lean, and compare. quorum's input space is small
structured data (a set of uint64 IDs plus a `uint64→bool`/`uint64→Index` map),
so exhaustive-ish differential fuzzing over small sizes is tractable and gives
real "green ⟹ covered" confidence. This is more direct and higher-confidence
for quorum than the random-whole-program generators (Microsmith/GoSmith) the
roadmap earmarks for later, and can reuse the same feature-tagging.

A failure in Layer 3 localizes via the Layer-1 case for the offending feature;
Layer 1 without Layer 3 proves features work in isolation but not in
composition; Layer 3 without Layer 1 finds bugs but not their cause. All three
are required for the sufficiency claim.

### Coverage status (2026-07-18)

Idiom coverage for the verification-relevant quorum target is **complete** in
the corpus (all `quorum`-tagged; run `scripts/coverage run --tag quorum`). Every
case is Go-oracle-green and currently frontend-export-blocked under Gobra — the
exact target set for the native frontend.

Idioms covered: defined types over uint64/uint8/map/array; value-receiver
methods on defined map/primitive/array types; multi-value-return methods;
the `AckedIndexer` interface + dynamic dispatch (hit/miss); `map[K]struct{}`
sets; nested defined types (`map[uint64]Index`); map range + comma-ok;
comma-ok from method/interface calls; nil-map zero-value reads;
`make([]T,0,cap)`/`make([]T,n)`; on-stack-else-heap slice with fill-from-right;
array indexing and range over a defined array (`JointConfig`); `len`; the
`n/2+1` threshold; defined↔underlying + narrowing conversions; typed
`1 + iota` on a defined type.

Edge probes: VoteResult across won/lost/pending/tie/exact/one-short and the
threshold at n=1,2,3(odd),4(even),7(on-stack),8(heap); CommittedIndex at
empty→MaxUint64, median, unacked-drags-median, n=1 acked/unacked, all-unacked;
Joint agree/disagree-lost/disagree-pending/both-pending, committed-min,
ids-union; MaxUint64 and uint8 wrap through conversions and the observation
pipeline.

Still frontend/extern-pending (not corpus gaps): `slices.Sort`-faithful
CommittedIndex (lands with the extern; the hand-rolled sort already pins the
algorithm), and the display functions (`String`/`Describe`,
`[...]uint8{}` literal, function-local struct type) which are not
verification-relevant.

### Buildout order

Add the Layer-1 gap cases as the matching frontend slice reaches them (a slice
is not done until its feature's isolated case and edge cases are green under
`GOLEAN_FRONTEND=native`). Layer 3 lands with slice 4/5, once methods on
defined types and the needed externs exist.

## Extern / stdlib policy

- Model only what the verification-relevant core needs. `math.MaxUint64` is a
  constant → inline. `slices.Sort` on `[]uint64` → a modeled builtin/extern
  with a differential test, or desugared during lowering.
- Display/formatting stdlib (`fmt`, `strings`, `strconv`) is out of scope for
  the core; the functions that use it are not verification-relevant. If a case
  needs them, classify frontend-blocked, do not approximate.
- Record every extern decision (name, signature, model) in a ledger.

## Slice plan (each a differential milestone)

0a. **[done 2026-07-18] Foundation proof**: `tools/nativefrontend` parses +
   type-checks with `go/parser`/`go/types`/`importer.Default()`. Verified it
   resolves defined types, non-struct-receiver methods, and interface
   method-sets on real corpus files *and type-checks the entire real
   `deps/raft/quorum` package* (multi-file, all stdlib imports resolved). No
   parser to build; the target's full type structure is available up front.
0b. **Vertical slice**: define the native wire schema (`GoLean/NativeJson.lean`)
   + `GoLean/NativeToIR.lean`; the exporter emits it for one trivial function;
   passes a native json-check, lowers, and matches the Go oracle under
   `GOLEAN_FRONTEND=native`. Proves the full pipeline end to end.
1. Scalars, control flow, direct calls → parity on the arithmetic/if/loop slice
   of the corpus.
2. Structs, pointers, arrays, slices, maps → parity across those corpus areas.
3. Defined types + value-receiver methods → the shape quorum needs.
4. Multi-package + package export batching → run the quorum package itself.
5. `math.MaxUint64` + `slices.Sort` externs → `MajorityConfig.VoteResult` and
   `CommittedIndex` differential-tested against Go.

Do not build ahead of validation. Each slice lands green (or with honest,
recorded frontend-blocked classifications) before the next.

## Out of scope (for now)

- Interfaces/method-set dispatch beyond what a stage demands (Phase 5 of the
  semantics upgrade is still frontend-gated; the native frontend will *supply*
  the type-decl and method-set metadata that unblocks it, but the interface
  semantics themselves are separate work).
- Concurrency (`node.go`, channels) — the raft ladder's final stage.
- Display/formatting stdlib models.
- Performance of the exporter.

## Parity status (2026-07-18)

Native pipeline is proven end-to-end and extends one construct at a time.
**ints is at full parity (26/26).** The whole scalar / control-flow / memory /
call core works: functions, `:=`/assign/multi-assign, if/for, arithmetic,
comparisons, conversions, blank targets, named types + type table,
struct/array literals, field/index access, address-of, deref, **A-normal-form
method and function calls** (`x.M(...)`, `&T{...}`), the empty struct `struct{}`,
and `len`/`cap`. Verified: a method call through ANF returns the right value;
the real `deps/raft/quorum` package type-checks.

Remaining blockers, each a bounded increment: **range** (unmodeled in GoCore —
see decision below), map literals + comma-ok + `make`/`delete`, slice literals
+ `make`/`append`/slice-expr + `slices.Sort` extern, func values/closures,
switch, goto/labels, defer, select. Quorum needs range + map ops + slice ops
on top of what works.

## Design decisions and open questions

Recorded as they arise (per the CLAUDE.md "capture decisions in files"
practice). GoCore is reshapeable — judge it by whether it supports reasoning
and clean emission (user steer, 2026-07-18).

- **[decided] Clean native wire + `NativeToIR` adapter**, not the Gobra wire.
  See "The contract" above.
- **[decided] Wire = typed Go AST; GoCore desugaring lives in `NativeToIR`
  (Lean).** Keeps the Go emitter a mechanical serializer and the semantic
  mapping inspectable in Lean. Every expression node carries its resolved
  `go/types` type.
- **[decided] Constant folding on the Go side.** Constant expressions
  (`-7/3`) are folded via `go/types` (no runtime division), matching Go.
- **[DECISION POINT, reached 2026-07-18] Calls-in-expressions / A-normal form.**
  GoCore has no call expression — calls are statements only, and the same is
  true of allocations (`newValue`) and other effects. The native frontend now
  covers the whole scalar/control-flow/memory core, and the *entire* next
  blocker set is effects-in-expression-position: method calls
  (`x.M(...)`), nested function calls (`f(g())`, `x + foo()`), `&T{...}`
  (address of a composite = allocate + address), and func-value calls. All of
  these are essential for quorum.

  Two ways forward:
  - **(A) A-normal form in the frontend (recommended).** A normalization pass
    hoists every call / allocation out of expression position into a preceding
    let-bound temp statement, leaving GoCore expressions pure. GoCore is
    unchanged. ANF is the standard verified-compiler normal form and is *good
    for reasoning* — it matches Goose/Perennial let-binding and is WP-friendly,
    which serves the "GoCore must support reasoning" test. Cost: one frontend
    normalization pass that must respect Go's left-to-right evaluation order
    and short-circuiting.
  - **(B) Add call/alloc expressions to GoCore.** The frontend stays a direct
    map. Cost: GoCore's expression language gains effects, which complicates
    the relational semantics (evaluation order and effects inside expressions)
    — worse for the reasoning story.

  Recommendation: **(A)**. It keeps GoCore's expression language pure and
  reasoning-friendly (the user's own criterion), matches the Goose/Perennial
  precedent GoCore already follows, and confines the complexity to the
  replaceable frontend. This is a reasoning-affecting architectural choice, so
  it is surfaced to the user rather than taken unilaterally.
- **[decided] A-normal form** (2026-07-18, user): implemented. Calls/allocs in
  expression position hoist to let-bound temps; short-circuit RHS and loop
  conditions are guarded (fail closed) to preserve evaluation order. Method
  calls unify as calls to `RecvType.M` with the receiver prepended.
- **[DECISION POINT, reached 2026-07-18] `range` / map iteration in GoCore.**
  GoCore has *no* iteration construct, and Gobra never lowered `range` either
  (the `range/*` corpus cases are frontend-blocked in the baseline). So `range`
  is an unmodeled GoCore feature, not just a frontend gap, and it is required
  for quorum (`for id := range c`). Adding it is a GoCore-shape + semantics
  decision:
  - **What to add:** a range/iteration construct over slices, arrays, maps,
    strings, integers (Go 1.22), and iterator funcs (Go 1.23). Slice/array/
    string/int ranges have deterministic order and are straightforward.
  - **The real question is map iteration order.** Go map iteration order is
    nondeterministic. The coverage ledger already lists "map iteration order"
    as `deferred-nondet`. Options: (a) the executable interpreter picks a
    deterministic order (e.g. insertion or sorted) and the relational semantics
    permits any permutation — quorum's uses are all order-insensitive
    (count/sort), so a deterministic executable order gives correct
    differential results while the relation stays honest about nondeterminism;
    (b) restrict the default lane to order-insensitive map-range observations
    (already the corpus policy) and model map range with a chosen deterministic
    order under the hood. Both keep the reasoning story clean (the relation
    allows any order); they differ mainly in interpreter policy.
  - Recommendation: add the range construct with a deterministic executable
    map-iteration order (option a), documenting it as an executable policy the
    relational semantics generalizes — mirroring how append-growth is handled.
    This is a GoCore change affecting reasoning, so it is surfaced to the user.

## Handoff

Persistent handoff for this effort: `docs/native-frontend-handoff.md` (create
before the first nontrivial pause). Same format discipline as the semantics
upgrade handoff.
