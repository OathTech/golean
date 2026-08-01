# Go differential fuzzer — side-project brief (2026-08-01)

The founding spec for a SEPARATE project (own repo, own agent loop): a
csmith/rustlantis-class differential fuzzer for Go, testing GoLean's
interpreter against `go run`. This document is the ONLY coupling to the
GoLean repo: it pins the interface contract and the acceptance tests.
Copy it into the new project verbatim as its founding doc; changes to
the contract happen HERE first (this repo is the record).

Prior survey: `docs/archive/differential-testing.md` (GoSmith vs
Microsmith). Decision: **fork Microsmith** (`ALTree/microsmith`) behind
a feature filter, rather than build a generator from scratch — it
already generates valid, typechecked Go via `go/ast` and is actively
maintained. A custom fragment-exact generator remains the recorded
fallback if the filter fights Microsmith's architecture (reassess at
M1).

## Goal / non-goals

GOAL: generate small valid Go programs INSIDE GoLean's supported
fragment, run them under both `go run` and GoLean's differential
harness, and surface divergences — especially SILENT WRONG ANSWERS
(both sides "ok" with different values), the class hand-written corpus
cases structurally under-sample.

NON-GOALS: compiler-crash hunting (Microsmith's native mode),
performance testing, concurrency/schedule fuzzing (that is GoLean's
R5 Choices-generator work, a different mechanism), coverage of Go
outside the declared fragment (out-of-fragment generation is WASTE,
not signal — the boundary refusals are already pinned by hand).

## The decoupling contract

The fuzzer treats GoLean as an external system-under-test:

1. **Private clone; HEAD by default, pinned when it matters.** The
   project lives at `side/gofuzz/` in the GoLean directory (own git
   repo; gitignored by GoLean; placed there so the sandbox workdir
   grant covers it). Its `golean-sut/` clone of the local GoLean repo
   is refreshed to HEAD at session start (finds land on fixable code);
   a specific commit is pinned only to reproduce a reported finding or
   to run the M2 rediscovery windows. The clone is never edited; the
   GoLean working repo is never touched. Day-to-day process:
   `side/gofuzz/CLAUDE.md`.
2. **The invocation.** From the clone root:
   `scripts/diff-coverage <manifest.tsv>` — the manifest is the entire
   input interface. Row format (TAB-separated):
   `id  go_dir  function  args  expected_status  features  expected_reason`
   - `go_dir`: directory containing a single `main.go` (package main),
     relative to the clone root — the fuzzer writes its generated cases
     under `<clone>/Corpus/fuzz/<batch>/<case>/` (gitignored territory
     is unnecessary; the clone is disposable).
   - `function`: the subject function the harness drives (exported
     results become the observation).
   - `expected_status`: `ok` or `panic` — from the fuzzer's own
     `go run` pre-pass (the oracle knows).
   - `features`: comma tags from the clone's `Corpus/coverage/tags.tsv`
     vocabulary (the generator's feature filter should be DEFINED in
     terms of these tags so findings map onto GoLean's ledger).
   - Results land in `artifacts/coverage/latest.tsv`
     (`result  id  features  stage  detail`) — `PASS` = agreement;
     `FAIL` + stage `differential`/`lean-observation` = the finds;
     stage `frontend-export` = out-of-fragment (generator bug or
     filter gap — track the rate, keep it near zero).
3. **Findings flow BACK as corpus-format case dirs** (main.go +
   cases.tsv, minimized) — GoLean imports them wholesale as guardrail
   cases. That is the entire reverse interface.

## The fragment (generation whitelist)

Generate ONLY: package main, single file; ints of all fixed kinds +
bool + string; arithmetic/comparison/bitwise/shift ops; if/else, while
loops (`for cond {}` and C-style `for`), labeled/unlabeled
break/continue, switch (value switches; NO type switches); functions
with multiple params/results, closures (lambda-lifted fragment:
capture by reference), defer/panic/recover; arrays, slices
(make/append/copy/len/cap/slicing incl. 3-index), strings (index,
slice, concat, len, byte/rune conversions), maps (make, literal,
index/comma-ok, assign, delete, len, `range` — see determinism rules),
structs (literal, field access/assign, pointers to), pointers
(& and *, incl. through struct/array/slice elements), defined types
(`type T <underlying>`) with methods (value AND pointer receivers),
interfaces (declaration, implicit conversion, method dispatch, type
asserts one- and two-result), `slices.Sort` on integer-element slices,
`min`/`max`, integer conversions.

EXCLUDE (fail-closed in GoLean today — generating them is waste):
goroutines/channels/select, floats/complex, generics/type params,
type switches, method values/expressions on interfaces, anonymous
non-empty interface types, embedded-struct method promotion, `goto`,
multi-value assignment from calls into interface-typed targets, maps
with mutation DURING range (BUG-005 — allowed to generate mutation
NEAR range but not inside a range body over the same map), imports
other than `slices` (and only for `Sort`).

The filter must be CONFIG-DRIVEN (a tag-keyed whitelist file), so
bumping the pinned GoLean commit + widening the filter is a config
change, not a code change.

## Generator rules (the Go-specific pitfalls)

1. **Determinism**: every generated program must produce identical
   output across runs. Concretely: any observation derived from map
   ITERATION must be order-insensitive (fold with a commutative
   operation, or copy keys out and `slices.Sort` before observing).
   Self-check in the pipeline: run each program under `go run` 3×;
   nonidentical output ⇒ generator bug, reject the case.
2. **Termination**: all loops bounded by construction (rustlantis-style
   decreasing counters or hard iteration caps). The harness has
   timeouts, but a timeout is a wasted case, not a find.
3. **Observation**: the subject function returns its observables
   (ints/bools/strings/structs of same); prefer folding program state
   into a handful of scalar accumulators — the harness compares
   returned values (and panic messages, exactly). Deliberately
   generate BOTH ok-paths and panic-paths (index OOB, nil deref, map
   unhashable, division by zero, explicit panic+recover) — panic
   IDENTITY (the message) is compared, and message fidelity is a real
   defect class GoLean tracks.
4. **Size**: small (tens of statements). Divergence value comes from
   CONSTRUCT COMPOSITION, not program length; small cases minimize
   almost for free.
5. **Shrinking**: on divergence, minimize before reporting (drop
   statements/simplify expressions while the divergence — same
   result+stage+detail class — persists, re-checking under both
   sides). A find without a minimized reproducer is half a find.

## Milestones — how we know the prototype is on track

- **M0 (generator sanity, no GoLean needed):** 1,000 generated
  programs; 100% compile + typecheck; 100% deterministic under the 3×
  `go run` check; ≥30% exercise ≥3 distinct feature-tag families.
  Deliverable: the batch + the rates.
- **M1 (harness integration):** the same batch through the pinned
  clone's `scripts/diff-coverage`; acceptance: ≥90% of cases reach
  `PASS` or a `differential`/`lean-observation` FAIL (i.e., the filter
  keeps generation in-fragment — `frontend-export` rate <10%), zero
  harness errors. Deliverable: the classification split.
- **M2 (THE VALUE TEST — historical-bug rediscovery):** point the
  fuzzer at OLD pinned GoLean commits where later-fixed silent-wrong-
  answer bugs were live, and rediscover them blind. Targets (verify
  each window first by running its known pinned case at that commit):
  - vacuous interface satisfaction (`x.(error)` wrongly true) — live
    in `85f3659..c22bc18`;
  - variadic-blind interface satisfaction — live in
    `85f3659..bfe5496`;
  - compound unhashable map keys silently accepted — live in
    `85f3659..c22bc18`;
  - nil-map unhashable-key lookup not panicking — live before
    `c22bc18`.
  Acceptance: ≥2 of 4 rediscovered blind (generator + filter tuned
  only on M1 data, no peeking at the bug list) within a bounded budget
  (say 50k cases each). This is the direct measurement of the thing
  the fuzzer exists for; if it can't rediscover known bugs, it won't
  find new ones.
- **M3 (production):** run against GoLean HEAD; triage every
  divergence as (a) real semantic defect, (b) message/fidelity gap, or
  (c) filter misclassification; deliver (a)+(b) as minimized
  corpus-format cases. Steady state: nightly batch, findings-only
  reporting. Acceptance for "worth keeping": any confirmed (a)-class
  find, or three (b)-class, in the first week of nightly runs — else
  the fragment is as tight as the corpus already made it, which is
  itself a publishable-grade negative result worth recording.

## Risks, recorded

- Microsmith's generator may resist tight fragment filtering (it
  targets breadth); the M1 `frontend-export` rate is the tell, and the
  custom-generator fallback is the recorded plan B.
- Map-order nondeterminism is the classic false-positive source; the
  3× determinism pre-pass is load-bearing — do not skip it.
- The pinned-commit discipline is what keeps the projects decoupled;
  resist any convenience edit inside the clone (if the harness needs a
  change, it is a GoLean change, made in GoLean, and the pin bumps).
