# Oracle panic/fatal classification: production candidate

> **Landing preface ([AGENT] landing worker, chunk L4 `land/observer-terminal`,
> 2026-09-07).** This file is the sprint's design record, landed VERBATIM below
> this block from branch `typed-consumer-sprint` (archive tip `7edc298f`,
> `docs/ARCHIVE.md`); the landing note is
> `docs/2026-09-07_land-observer-terminal.md`. Where this record and the landed
> code differ, the landed code is: (1) the same-run crash channel is MANDATORY
> on every stderr-classifying query (landing review finding A-R6) — the "strict
> raw fallback" for an empty acknowledgement that this record describes did
> NOT land; a pre-`main` abort (package initializer or `init()` aborting before
> `main`'s first statement) refuses by name and its rows are red on BUG-107's
> `Cases:` line; (2) a runtime chain-shape pin (inside a channel copy every LF
> before the trace header is TAB-followed, the runtime's single `[signal …]`
> line excepted). The `docs/evidence/2026-09-06_observer-*` directories this
> record cites stay on the archive branch (they do not land — [USER] ruling of
> 2026-09-07, relayed, `AGENTS.md` "Evidence on main"). The two gate scripts it
> names (`scripts/check-observer-controls.py`, `scripts/check-observer-tools.py`)
> did not land in this chunk (landing note, "What did NOT land"); the harness's
> Go tests run under `scripts/ci` instead.

2026-09-06. [AGENT] typed-contract-review. **Bounded independent production
review PASS (`1bd2022b`), fresh full differential measured and narrowly
reconciled, final ordinary CI PASS.** Main is unchanged.

The prior classifier accepted a fatal unwind as a panic, and an intermediate
system-trace classifier still read program-printed panic text as the actual
payload while discarding output. The minimal red regression was
`print("panic: forged\n\t"); panic("actual")`: it returned message
`forged` with empty output. The fresh kernel-free Go unit regression failed
with exactly that value before the replacement. Independent findings and
the stopped, incomplete full run remain in the evidence directory.

The replacement implements the independently reviewed
[crash-channel design](2026-09-06_observer-crash-channel-design.md):

- The oracle installs `runtime/debug.SetCrashOutput` before calling the
  subject, without a recover/defer wrapper. The runner resets owned report
  and acknowledgement files before every plain/race draw. Setup failure
  exits the child with 78, preserving `go run`'s exit and yielding a named
  setup refusal.
- `crashview.go` gives kind, first-line message and output a shared checked
  view. The complete report must be a byte-identical stderr suffix, before
  UTF-8 validation or JSON encoding. Its raw first runtime origin uses the
  pinned same-execution system traceback contract. Program output is the
  exact prefix before that suffix.
- Malformed/missing paired evidence, failed registration, unknown origins,
  additional report markers after the origin, corruption and suffix mismatch
  refuse. Successful observations require registration and an empty report.
- Fatal messages precede the runtime's crash-copy boundary. Their fallback,
  and init panics before registration, count all raw markers with no
  continuation exemption. Ambiguous payload/output is a named observation
  refusal; terminal kind is never guessed from the expected manifest status.
- `--copy-oracle` inserts the same hook into a fresh diagnostic oracle
  package copy. AST positions locate the real main opening brace; all other
  source bytes remain exact. It refuses missing/duplicate main, reserved
  helper collisions and reused output directories. Diagnostic runner wiring
  is a separate increment; its semantic frontend sources must stay intact.

No GoCore semantics, UTF-8 replacement policy, payload boxing identity,
Go toolchain pin or race observation policy changed. The owned file is a
trusted runtime transport, not cryptographic authentication of caller-forged
matching capture files. Runtime configuration, arbitrary file/fd manipulation
and resource-accounting effects remain outside the admitted source domain,
as explained and probed in the design. O2 admission retains arbitrary string
bytes and repeated panic; invalid-UTF-8 text membership is a separate R-1
obligation, not silently decoded here.

## Measured evidence at this checkpoint

`docs/evidence/2026-09-06_observer-classification/` retains source-bound logs,
raw counterexamples, prototype history and the following production results:

1. `minimal-red.log`: fresh Go test fails on the pre-repair source with
   message `forged`; the same test passes with the new strict fallback.
2. `hybrid-gate-final.log`: fresh helper build/unit tests, 47 extracted
   strict/sampling controls, 28 actual Go plain/race controls, two actual
   setup-IO failures, and 11 compiled corruption mutations rejected. The
   final run is under a verified 16 GiB cap and Lean threads 3; this matters
   because shell controls also invoke the existing Lean JSON comparator.
3. `focused-hybrid.tsv`: fresh Go/Lean run, 23 rows = 22 PASS and one
   FAIL/go-observation. All eleven marker rows include the minimal
   print/literal pair, glued output and a complete printed fake trace. The
   nine existing byte controls and two simple sync fatals also pass.
4. `hybrid-full-initial.tsv` and `.meta.tsv`: the fresh complete corpus,
   3,627 rows = 3,382 PASS / 245 FAIL. Exactly eleven new marker PASS rows
   and the one existing failed observation below; no other result or
   unapproved stage changes and no removals. All sixteen frozen production
   source hashes were rechecked after the run. The original baseline and
   complete delta are preserved before narrow reconciliation.
5. `ci-hybrid-initial.log`: terminal exit 1, with the expected raw baseline
   drift, a BUG-106 metadata punctuation error, and six stale sampling
   self-tests (S1–S6) whose synthetic successful oracle omitted the required
   registration acknowledgement. The metadata and success mocks are repaired
   separately; the production classifier and full-run source remain exact.
6. `lane-validation-fixed.log`: the affected full `--with-go` self-test exits
   0, reaching every intended sampling assertion. The four-line synthetic
   success correction has independent source review PASS `198aee9f`.
7. `ci-hybrid-final.log`: final ordinary CI exits 0, including warning-free
   core build, fresh interface/admission audits, observer controls, 202 eval
   tests, all 394 negative cases and the complete retained 3,627-row baseline.
   `hybrid-final-source-addendum.json` binds the unchanged production sources
   and separate mock/baseline/BUG corrections. The full corpus was not rerun
   merely to clear metadata or test-mock errors.

The exact changed existing row is
`sync/mutex-unlock-fatal/during-panic-unwind`: previous PASS/stage `-` →
FAIL/stage `go-observation`, cause `ambiguous fatal message/output before
m.dying`. This reveals a lost authenticated observation. Independent design
review `aafe225b`, explicit fidelity-boundary disposition `ab2ad4d5`, and the
root coordinator endorse that correction under K3/fail-closed. The refusal
is not conformance, not a GoCore terminal and not B7 equivalence drift.
The fresh full differential measured exactly that row/stage change. The
baseline records it as a FAIL; no refusal has been relabelled as conformance.

Relevant commands from this worktree:

```sh
env GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped \
  python3 scripts/check-observer-controls.py
env GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2 \
  GOLEAN_COVERAGE_ARTIFACTS=artifacts/observer-classification/focused-hybrid \
  scripts/capped scripts/coverage run \
  --prefix panic-recover/panic-markers/ \
  --prefix panic-recover/panic-controls/ --prefix sync/mutex-unlock-fatal/
```

The first command exits 0. The focused differential exits 1 because its
explicitly reported refusal remains a failed observation. Neither that
result nor the earlier stopped full run is a green full baseline.
