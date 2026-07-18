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

## The contract: reuse the existing wire ADT

**Do not change GoCore or the lowering.** The native frontend emits the same
strict wire JSON that `GoLean/GobraJson.lean` decodes and `GoLean/GobraToIR.lean`
lowers. This is the whole point of the frontend/wire/GoCore isolation the
architecture already bought: the frontend is a replaceable component behind a
stable schema.

- Target schema: the `Document` → `Program` → `members`/`types` shape in
  `GoLean/GobraJson.lean`. Known-good examples live under
  `artifacts/coverage/work/<case>/main.go.internal.json` (Gobra-produced).
- The strict Lean decoder is the schema authority. The native exporter is
  correct when its output passes `golean gobra-json-check` and lowers/executes
  identically to the Go oracle.
- Where the wire ADT carries Gobra-only fields (assertions, proof members,
  spec origins), the native exporter emits the empty/absent forms. Where Gobra
  mangles names, the native exporter emits clean source names — lowering
  already canonicalizes both, so cleaner input is strictly better.
- If a needed Go construct has no wire representation, extend the wire ADT
  (and its Lean decoder) deliberately, fail-closed, rather than approximating.

Location: `tools/nativefrontend/` (Go program, go/ast + go/types). The harness
selects it via `GOLEAN_FRONTEND=native` (the switch already exists in
`scripts/diff-coverage`; default stays `gobra`). Gobra stays alive in parallel
until the native path covers the current 136 with no regression.

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

**Gaps — no isolated case exists, must add** (canonical Go + `cases.tsv`;
frontend-blocked until the native frontend lowers them, which is expected and
correct — the corpus is frontend-independent):

1. Defined map type: `type M map[uint64]struct{}`.
2. Value-receiver method on a defined map type: `func (m M) F() ...`.
   **Corpus-wide there is currently no method on any non-struct receiver** —
   this is quorum's central idiom and the single most important gap.
3. Value-receiver method on a defined primitive type: `type Index uint64;
   func (i Index) F() ...`.
4. Defined array type over a defined type: `type J [2]M`.
5. `map[K]struct{}` set idiom: empty-struct value, membership via comma-ok and
   range.
6. Nested defined types: map value is itself a defined type (`map[uint64]Index`).
7. On-stack-array-else-make idiom: `var stk [7]uint64;
   if len(stk) >= n { s = stk[:n] } else { s = make([]uint64, n) }`.
8. Fill-from-right into a slice, then sort, then index the median
   (the `CommittedIndex` core) — depends on the `slices.Sort` extern.

### Layer 2 — edge enumeration (souped up)

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

0. **Vertical slice**: exporter emits wire JSON for one trivial function
   (e.g. an `add`), passes `golean gobra-json-check`, lowers, and matches the
   Go oracle under `GOLEAN_FRONTEND=native`. Proves the architecture end to end.
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

## Handoff

Persistent handoff for this effort: `docs/native-frontend-handoff.md` (create
before the first nontrivial pause). Same format discipline as the semantics
upgrade handoff.
