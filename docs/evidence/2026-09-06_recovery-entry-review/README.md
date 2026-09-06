# Independent recovery entry/storage review

2026-09-06, typed-preflight. **Bounded PASS** for the seven frozen setup/entry
modules, their tests and dedicated audit over storage base `4f7aedef`. This is
an entry contract, not O2 completion, whole-control preservation, terminal
rendering, Iris ownership, WP, termination or stable-facade acceptance.

The exact 13-file author manifest is retained as `frozen-source.sha256`, verified
against the reviewed worktree. `source.tar.gz` preserves those bytes. Existing
storage/static dependencies are supplied by the named base and checked by the
dedicated audit's complete imported-local-origin sweep. No semantic source or
gate was edited by this reviewer.

I read `RecoverySetupShape`, `RecoveryInitialization`, `RecoveryResultRoots`,
`RecoverySetup`, `RecoverySetupWf`, `RecoverySetupReadout`, `RecoveryCallEntry`,
the underlying typed heap/environment/argument definitions, the claim ledger,
tests, and both audit implementations. The important contract boundaries hold:

- `setup_typed_wf` derives actual `runProgramSetupM` success from independent
  admission for every fuel/choice stream. There is no assumed setup success,
  future safety or custom evaluator. No globals/init means the setup consumes
  no fuel or choices. Complete argument vectors prevent zip truncation.
- Exact canonical equations preserve incoming Boolean values and initialize
  Boolean/payload result cells to false/nil. Pointwise readout is bounded by
  explicit length/index premises. Pointer-root declarations have no fabricated
  nil zero in this restricted storage profile.
- Static ordered lookup is connected to reverse declaration order using
  signature/block-key distinctness. Heterogeneous outer shadowing remains
  legitimate; the separate all-bindings predicate still bounds hidden roots.
- `enterFrame_typed`/`enterFramePick_typed` use actual function lookup, program
  typing, current heap and typed complete arguments. Empty method metadata
  makes dispatch inert; successful entry is `Result.ok`, preserves all choices,
  extends the world, and establishes the real callee environment and result pins.
  World extension preserves address typing, without granting exclusive ownership
  or claiming preservation of arbitrary future cell values.

The first-match/static ordering lemmas and explicit result readout are useful
consumer facts. The canonical result-location equation already fixes distinct
allocation indices; the generic `ResultRoots` predicate itself does not imply
distinctness or exclusivity. The ledger does not incorrectly claim it does.

## Independent probes

`Probes.lean` freshly elaborated via the author's capped, pinned environment,
with the source and log stored only in this review worktree:

```sh
GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 scripts/capped lake env lean \
  /home/dev/projects/golean/.claude/worktrees/typed-preflight/docs/evidence/2026-09-06_recovery-entry-review/Probes.lean
```

Exit 0, `probes.log`. Eight independent kernel theorems exercise:

1. A new admitted function with two captures aliasing the same live Boolean;
   the generic entry theorem preserves their typing and the supplied choice list.
2. Its actual `enterFrame` allocates separate slots 1 and 2 containing pointers
   to cell 0, preserves cell 0, and allocates the false result at slot 3.
3. Nil cannot satisfy live-root argument typing.
4. A dangling capture cannot satisfy typed arguments.
5. A truncated complete argument vector cannot satisfy `ParamsValues`.
6. Pointer-root results cannot acquire a fabricated nil `ZeroValues` witness.
7. A valid visible lookup cannot hide a dangling outer binding.
8. Initialized false/nil results cannot be read as true/nil.

The axiom output for every probe contains at most propext, Classical.choice and
Quot.sound. These are semantic predicate/application checks, not new native Go
conformance results. No duplicate expensive full differential was run.

## Audit and author validation

The post-import audit requires 37 named theorems, verifies all nine module
origins are present, and scans every constant from all imported GoLean/Tests
modules plus the active module. It permits only the existing classical trio.
Each of seven semantic modules is poisoned independently; unused private audit
and trailing test declarations supply two further controls. The poison compiles
before the checker must reject the named forbidden axiom. There is no allowlist
restricted to named exports and no pre-import audit blind spot.

The inspected final dedicated log (`setup-gate-2.log`) records 37 exports,
11,241 checked constants, all nine compiled poison rejections, and PASS. It
includes 14 shipped kernel regressions and the private generic setup witness.
The author's ordinary CI log also ends PASS, explicitly using cached full/negative
renderer records; it is not a fresh full-corpus run for this increment. Those
logs and the source-bound reuse record are copied as supporting evidence.

The remaining migration/integration obligations are explicit in the reviewed
ledger: B7 must remove representation-enforced context equalities and preserve
the actual setup/call semantics; public promotion must extend facade/audit
coverage and receive its own review. Full control, terminal and Iris claims
remain separate work. No new critical decision is identified by this review.
