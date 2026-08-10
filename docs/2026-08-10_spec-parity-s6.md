# Spec-parity slice 6 — equivalence minors (2026-08-10, branch `spec-parity-s6`)

The charter amendment's slice (user-approved 2026-08-10;
`docs/2026-08-09_spec-parity-arc-charter.md`, "Amendment … slice 6" —
items 1–3 here; item 4, the BUG-053 class-closure delta review, folds
into this slice's AUDIT, not this build log). Branch off `spec-parity`
@ c6eedd4b. RECORD-HOME CALL, recorded: this dated note is the slice-6
build log (the wp-walk-driver note is S3's dated record and items 1–2
are not driver work); the manifest and matrix carry the per-row state,
as always.

## Item 1 — the fuel-independence lift (commit 97421952)

- **Found on arrival**: `execProgLoop_mono` — the lemma the amendment
  says to prove — was ALREADY SHIPPED (`GoLean/GoCore/MultiStreams.lean`,
  Audit-guarded, consumed by every `TerminatesNormallyC`). The owed
  piece was the LIFT itself, and the ∀-fuel forms need a lemma mono
  does not give. Recorded here rather than silently re-proved.
- **New lemmas** (all in `MultiStreams.lean` beside their kin;
  THEOREM-only additions — no executable changed, the module is
  import-downstream of `Multi.lean`, so the differential surface is
  untouched by construction; all constructive `[propext, Quot.sound]`,
  Audit-guarded + anchored):
  - `execProgLoop_le` — sub-bound classification: truncating a
    completed pool run's fuel yields the same `.ok` or
    `.error .fuelOut`, NEVER any other outcome. Matrix §7.2's
    truth-equivalence argument ("sub-bound runs classify `fuelOut`,
    never `.deadlock`"), machine-checked.
  - `stepAllBranchesOk_mono` + `allStreamsOkPool_mono` — checker
    fuel-monotonicity (the checker only returns `true` by reaching
    terminal pools, never by spending slack).
- **The regeneralized bundle** (`Specs/GooseParityChannels.lean`, all
  six rows): `<row>Cert`/`<row>AllSchedules` now in the
  `∃N, ∀ fuel ≥ N` form `TerminatesNormallyC` uses;
  `<row>NoDeadlock`/`<row>NoRace` at ALL fuels (strictly stronger than
  the amendment's ∃N ask, licensed by `execProgLoop_le`). The kernel
  `decide +kernel` evidence is preserved per row as `<row>Cert<bound>`
  (bounds 200/400/800 unchanged — no new decide propositions were
  introduced, so no new #eval was owed; the literals re-elaborate the
  already-shipped kernel checks). Kit derivations (`chanCert_*`)
  regeneralized to match. Certs stay constructive
  `[propext, Quot.sound]`; the derived members the classical trio.
- **Name-stability check, performed**: none of the regeneralized names
  is among the 44 designated (`proofs/Audit.lean` designated list read
  directly; the fork/join family O8 IS designated and was NOT
  touched). `dspCert`/`dspAllSchedules` are designation CANDIDATES
  whose statements changed — allowed (candidates, not designated); the
  charter's candidate table now points at the fuel-free forms, which
  are the better curation shapes. Scope note: "and siblings" read as
  the sibling namespaces inside `GooseParityChannels.lean` (trio /
  muxer / actris — exactly the 200/400/800 rows the amendment names);
  `GoldenSelectDone` is the checker-refinement witness, not a parity
  row, and keeps its literal-fuel statements (recorded, deliberate);
  the forkJoin family is designated and byte-identical.
- Records moved in the same commit: matrix §7.2 fuel paragraph
  (fuel is no longer an axis for the covered rows — the against-us
  axis removed), manifest FC3 fuel line. The module header's stale
  "1c5" ci-step label corrected to 3a2 in passing.

## Item 2 — P-S3-5 closed, the joint-carrier composition (commit c84d3af6)

- **Kit lemma** `goSpec_seeded_totalReadout`
  (`Specs/GooseParityKit.lean`): `GoSpec {r↦0} prog {r↦v}` + seeded
  `MachineWf` + the R2 ∀-streams `Terminates` pin ⇒
  `∃N ∀fuel≥N ∀ch, execStmt … = .ok (.normal σf, _) ∧ loadLoc σf 0 =
  int v` — completes-AND-verdict on the SINGLE sequential carrier
  (the `goldenTotalReadout` precedent shape; exactly the composition
  the S3 delta review machine-confirmed the two shipped halves could
  not make).
- **Six class-1 instances** (`<row>TotalReadout`: the 5 nil rows +
  block), each consuming its row's REAL R2 pin
  (`test…Terminates`/`blockTerminates`) — the instances are the
  discharge witnesses (every premise closed at a concrete program).
  Four more rode in with item 3's tranche rows (new ×2, vars ×2) —
  ten total.
- Audit block added with the scope-honesty language (name-existence
  tripwire; witness-citation content stays the pre-merge audit's
  job). Axioms: the classical trio (spec lane). Parity effect
  recorded at matrix §7.1: the "separate halves, conjunction
  informal" caveat now applies to the CONCURRENT rows only (their
  joint form needs the frame-quantified triple — P-S4-1/2, successor
  scope).

## Item 3 — the bounded driver tranche, P-S3-2 (commits aafab5f5 + d7a82ce1)

- **Tooling lever** (`scripts/gen-imported-pin`): the `.tmp` mkpins
  helper promoted to a tracked script per the parking ledger's open
  question — fresh emit + `NativeToIR` decode + repr, TotalPins seed,
  per-oracle R2 `Terminates` + verdict-1 readout pins at fuel 2000.
  Fail-closed scope: golean-boolean-oracle units only (authored
  wrappers refuse); #evals EVERY checker/readout Bool true before
  writing any `decide` (the eval-before-decide doctrine, mechanized at
  the generation step); never self-registers — the
  `check-imported-pins` PINS completeness cross-check stays the
  closing guard, and registration is a deliberate same-commit hand
  edit (its printed instructions).
- **Yield** (honest, budget-bounded): 2 units backfilled
  (semantics/new, semantics/vars — pins 9 → 11, unpinned 73 → 71);
  4 R3 rows proved at the full D1 pair + joint form —
  `testNilDefault` + `testNilVal` BOTH upstream-Qed (new.v:13/:19 @
  43d4efa; the arc's genuine parity-row count 2 → 4) and the two vars
  coverage rows; 1 oracle out-of-tranche with its reason
  (`testAddressOfLocal` — short-circuit `Expr.and`, the recorded law
  gap; hard bound honored, R2 pins shipped, R3 walk blocked, visible
  manifest + matrix rows); the 71-unit remainder recorded as
  NOT-REACHED (budget; figure corrected at the S6 audit — first
  written 69, a double-subtraction of the two newly pinned units), with only the SAMPLED blocker classes named
  (manifest slice-6 addendum — every figure's command emits it).
- **Driver notes for the next movement**: the S3 side-goal pattern
  held exactly (supplies: `wp_init_bool`/`wp_init_ptr`/
  `wp_new_value`/`wp_assign_store`/`wp_strict_apply_pure`/
  `wp_eval_strict_nullary_pure`); int inits and int applies auto-walk
  (a `wp_init` supply at an int local BURNS the heartbeat budget in
  `isDefEq` — the P-S3-4 failure shape, hit once and removed); int
  stores need one `show IntKind.normalize … from by decide` simp arg;
  deref-STORE (`Assignee.addr`) needs only `wp_assign_store` at the
  allocated address (the target-plan walk is automatic); the per-unit
  marginal cost was ~1 hour for the first unit, ~15 minutes for the
  second — the walk, not the pin, is now the cost.

## Gate state (every commit)

`scripts/ci` PASS at each of the four commits — proofs + in-build
Audit gate (axiom allowlist + non-vacuity + statement-TCB closure),
eval tests, imported-pins staleness guard (11 pins), negative diff,
baseline diff vs the tracked 1483-id baseline: **zero drift on every
prior id, zero new ids** (this slice adds no corpus cases; the
"explained pin-lowering additions" allowance went unused — pin
modules are proofs-side, not corpus rows). The full-differential line
is the recorded cached run, whose provenance the S6 audit made exact
(scoping correction, applied per its verifier): the run's meta label
`4e8a25e` is a PRE-COMMIT HEAD, not a tree identity — its
`git_dirty true` tree WAS the 8ebc0c9c class-closure content (the run
finished minutes before that commit, its 1364/119 figures match the
commit's own recorded `--slow` gate and the tracked baseline exactly,
and the commit's re-certified tier=slow records carry fresh
post-change wire-shas) — and the gate's "stale" marker compares only
the commit label against HEAD, never the tree. So the window that
must be surface-free is `8ebc0c9c..tip` (equivalently `c6eedd4b..tip`
— c6eedd4b is docs-only over it), which is the window argued below;
the audit fix round then re-ran the FULL differential fresh at its
own tip (gate record at the end of this note). The window argument,
stated per the S5 discipline: `git diff
--name-only c6eedd4b..<tip>` touches `GoLean/GoCore/MultiStreams.lean`
(THEOREM additions only — import-downstream of `Multi.lean`, no
executable definition changed), `proofs/`, `docs/`, and
`scripts/{gen-imported-pin,check-imported-pins}` (the guard script's
registry — exercised green in-gate) — no frontend, no interpreter, no
corpus: the differential surface is untouched by construction, which
is why no `--diff` run was owed (charter gate note honored). 44
designated statements byte-identical (no designated module in the
diff; ci name-list + closure gates green throughout).

## Parked / left open (with owners)

- The && / `||` short-circuit WP law family — UNCHANGED owner (agenda
  E); now blocks `testInterfaceNilWithType` + `testAddressOfLocal`.
- P-S4-1/2 (safety half, channel WP laws) — successor arc, unchanged.
- The remaining 71 unpinned units (corrected at the S6 audit; first
  written 69) — the lever is tracked tooling now;
  scheduling is the user's scale call (agenda item 9's residue).
- `GoldenSelectDone`'s literal-fuel statements — deliberate (item 1
  scope note); regeneralize only if it ever becomes a parity row.

## S6 audit fix round (2026-08-10; zero critical, zero surviving
major — every confirmed minor + surviving note kernel applied)

Four commits on `spec-parity-s6` after the slice record; findings and
verdicts in the audit task output (11 agents, verify phase per
finding). (1) The method-set record CLASSIFIER fails closed
(`methodSetCoverageForKind` — the inline `default: full` was the
retired blanket-true arm relocated to the emitter, latent; unknown/
empty kind and nameless TypeDefs now refuse the export; Go unit
fixtures pin every known kind + the refusals). (2) The dispatch-half
and renderer-half refusal arms PINNED (4 new MS eval pins with
mutation-sensitivity twins — 11 MS pins total; both arms previously
revertible past every gate). (3) The TSV read-loop trailing-newline
hole closed at all seven tracked/hand-editable-input sites (swept
list in the commit; gen-imported-pin fixture pair green), and the
generator's emitted seeds now carry `methodSets` (the recorded
divergence's forward fix; contract note §5). (4) Records truthed:
the six certificate fuel "minima" re-measured first-hand (86/65/71/
140/195/308 — the shipped figures were doubling-search round points;
manifest carries the emitting command), the 69→71 remainder figure at
five sites, new.v:9, the charter amendment's inline found-on-arrival
correction, the D3 candidate table moved with the `dspCert` split,
`execState_pin_eq`'s docstring, the window-argument scoping above,
and the contract note's new §5 known-limitations (seed divergence +
promoted-unexported re-keying).

**Gate at the fix-round tip (00948a30): fresh full
`scripts/ci --diff` PASS** — the classifier fix moves the frontend,
so the full differential was owed and ran FIRST-HAND: `baseline diff
FULL (1483/1483, no regression)`, NO stale marker
(`artifacts/coverage/latest.meta.tsv`: `git_commit 00948a30`,
`git_dirty false`, 1483 manifest cases = the full corpus;
`manifest_sha256 5dd06a6c…`), negative lane no regression, eval tests
136 ok (the 4 new MS pins included), every fixture suite green,
44 designated byte-identical (no designated module in any fix-round
commit; name-list + closure gates green). Zero drift with the
classifier change — as predicted: its new arms are refusals on shapes
the emitter never produces.

TERMINAL ANNOTATION on this note's "44 designated byte-identical"
claims (all true as written, of the BUILD slices): after this fix
round the user's D3 ruling (2026-08-10) designated the two candidate
pairs in their fuel-free forms — 44 → 48. The designation record is
the charter's candidate-table section; the execution (F4 hoist to
`Specs/GooseParityTargets.lean`, Challenge/Solution/judge-config/
statement-TCB wiring, closure-walk verification on all four) is the
designation commit on `spec-parity`.
