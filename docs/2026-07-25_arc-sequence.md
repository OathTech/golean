# Arc sequence toward the quorum pilot (2026-07-25)

Decided with the user 2026-07-25, immediately after the unwinding arc
merged (`main` @ 8d0bd8e; corpus 783/367). This is the planning record for
the next several arcs; each arc still gets its own dated design note when
it opens, and each ends with the standard gate + audit ask + merge
sign-off. Re-derived from: the failing-set composition (below), the
proof-corpus debt (`docs/2026-07-24_proof-corpus.md` §5), and what
`../deps/raft/quorum` actually needs (roadmap ladder stage 1).

## The two-track picture

"The Verdi results, but on real code" needs two tracks to converge:
**coverage** (real Go lowers and differentially validates) and **proof
depth** (the WP calculus can state and prove properties of what lowers).
Coverage has recently outrun the calculus — every W-rung merged since the
reshape owes its proof-corpus entry. The sequence below alternates: cheap
coverage wins first, then the calculus catch-up, then the big coverage
campaign, then the milestone that forces reality.

Failing-set composition at 783/367 (stage: frontend-export unless noted):
interfaces 48 (+6 backlog +5 lean-obs), generics 46 (deferred:
monomorphization), channels 38 (R4+), builtins ~50 (machine ops EXIST —
frontend emission only), constants/range/control-flow/slices/maps ~90
mixed small gaps, floats/complex 41 (deferred: IEEE doctrine), fidelity
backlog 64 (ratchet), incl. **8 differential-stage wrong answers** — the
only entries that are lies rather than gaps.

## The sequence

1. **Arc `wrong-answers-builtins` (THIS arc).**
   - Slice 0 — kill the 8 wrong answers (a visible red beats a hidden
     wrong answer; these are the system's only lies). They decompose:
     (a) 3 panic-MESSAGE fidelity gaps (`pointers/pointer-array-slice-bounds`,
     `strings/string-slice-bounds`, `strings/string-slice-low-high-panic`):
     our bounds messages lack Go's `[:3] with length 2` detail — fix the
     messages in `Ops.lean` to Go-exact, oracle-pinned;
     (b) 2 string-literal escape defects (`strings/literal-edge/interpreted-octal-hex-escapes`,
     `strings/string-escape-bytes`): the wire carries literal values as
     JSON strings, which cannot represent non-UTF8 byte sequences
     (`"\xff"` arrives as a replacement rune) — move literals to byte
     arrays on the wire (or bytes-when-not-UTF8), decode frontend-side
     with Go's exact escape rules;
     (c) 2 variadic spread bugs (`variadic/forwarding`,
     `variadic/no-args-vs-empty-spread`): `f(xs...)` forwarding and the
     nil-slice vs empty-spread distinction mis-lower;
     (d) 1 interfaces-lane mis-lowering (`interfaces/typed-nil-pointer-compare`):
     fail CLOSED now, real fix in the interfaces campaign.
   - Slice 1 — builtins emission: append/copy/delete/new (+ remaining
     len/cap forms) onto the EXISTING machine ops (`appendSlice`,
     `copySlice`, `mapAssign`-delete, `newValue`). Guardrails are the ~50
     blocked cases; per-rung edge batch per §6 practice.
   - Slice 2 — constants (const decls, iota) and the cheap range /
     control-flow gaps, same pattern.
   - Stretch (only if it fits cleanly): BUG-003's per-iteration loop-var
     desugar — also frontend-side.
   - Exit: ratchet moves DOWN from 64 for the second time ever; zero
     differential-stage wrong answers remain.

2. **Arc `proof-corpus-catchup`.** The calculus catches up with the
   machine: `wp_call_value` (call-through-value laws), defer-aware frame
   laws, ONE witnessed end-to-end spec through recover (a `GoFuncSpec`
   "returns 7 despite the panic"), the owed manifest entries for W1–W5 +
   unwinding (`docs/2026-07-24_proof-corpus.md` §5), and the
   granularity-ledger entries for the defer/panic chain ops (a named R4
   prerequisite). Non-vacuity discipline as always: law + witness in the
   same commit.

3. **The interfaces campaign (2–3 arcs).** The single biggest unlock (48+
   cases) and the raft blocker (`AckedIndexer`, `Storage` are
   interfaces). Fix defined-vs-alias identity properly (the BUG-004 root
   cause — `type T int` currently lowers as an alias, erasing identity);
   differentially validate the dormant Gobra-era machine half
   (`toInterface`/`typeAssert`/dynamic dispatch); add type asserts and
   type switches frontend-side. Flips the three interfaces-blocked reds
   from the unwinding arc (`panic-typed-nil-recover`, `recover-value`,
   `defer-interface-value-eval`) and the slice-0(d) fail-closed pin.
   Guardrails first: the blocked cases are the seed corpus.

4. **The quorum pilot (the milestone arc).** Roadmap ladder stage 1 on
   REAL etcd files: multi-package frontend; a minimal stdlib extern
   policy (`fmt`/`strings`/`sort` stubs — its own decision note first,
   incl. whether `slices`/`cmp` generic callsites get externs instead of
   monomorphization); order-insensitive map-fold observations; the actual
   `quorum` package through the differential against etcd's own test
   values. Exit: a proven property of the real `CommittedIndex` — the
   first "Verdi results on real code" artifact.

5. **R4 + R5 (goroutines, then the concurrency harness).** After the
   pilot proves the sequential story on real code. BUG-002 closes here;
   the unwinding arc already made panic per-goroutine-correct (the chain
   lives in the continuation). R5's Choices-generator harness gets its
   own design note per F4.

Deliberately excluded for now: generics (the pilot's extern-policy note
decides how far stubs reach before monomorphization is ever needed);
floats/complex (IEEE doctrine, own arc when something real needs them);
channels (R4+).

## Arc 1 build log (2026-07-26, completion)

- Slices 0–2 landed (12 commits before the audit): 8 wrong answers
  killed; builtins + conversions + const decls + range family (incl.
  range-over-string on `decodeRuneAt`) + per-decl quarantine + set of
  frontend fixes the guardrails caught (double-hoist builtins, Go 1.26
  `new(expr)`, generic-instantiation boundary). Corpus 374 → 470.
- **Pre-merge audit (user-approved full scale, 35 agents: 3 Opus
  reviewers + 2 refute-by-default Opus verifiers per finding): 11
  sustained = 7 distinct defects, 5 refuted, ALL addressed:**
  1. interface-conversion guard holes (returns, composite literals,
     map-assign, map-element multi-assign) — guard extended; BUG-006
     records the class and the one intentional PASS→FAIL it closed;
  2. pointer-array value ranges snapshotted — now read THROUGH the
     pointer each iteration (writes during the loop observed; nil
     panics at first read);
  3. ASSIGN-form range lvalue effects hoisted once — non-identifier
     targets fail closed;
  4. map iteration does not observe delete/clear — BUG-005 (snapshot
     semantics; machine fix is its own slice), two red pins;
  5. map-element lvalues outside single assignment die runtime-stuck —
     boundary refusal now;
  6. 3-index slice of an ARRAY said "capacity", Go says "length" —
     `checkSliceMax` parameterized;
  7. count-only ratchet launders equal-sized swaps — **the SET ratchet**
     (`baselines/untriaged-ids`, check-bugs 4b): new entrants fail the
     gate, departures must be removed in the same commit.
- End state: corpus **785 / 469** (the −1 is BUG-006's intentional
  flip), untriaged ledger **64 → 31** (18 mis-lowered cases now refused
  at the boundary), gate 12/12.
