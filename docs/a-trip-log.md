# A-TRIP unit log — the veneer tripwire (lane w1-prover, branch a-trip)

Charter: unit A-TRIP of the plan of record
(`docs/2026-08-28_iris-corpus-plan.md` §6.3; the ban it mechanizes: §2d).
Base: main @ c484cef9. One writer, this worktree only.

**Quantifier-audit line** ([AGENT], per charter): this unit advances NO
quantifier — it is the mechanized enforcement of §2d's proof-route rule.
LINEAGE: the project's own Audit statement-closure walker
(`proofs/Audit.lean`, statement-TCB gate), re-aimed from statement
closures at PROOF-TERM closures; divergence from the ancestor: theorem
VALUES are walked (the ancestor deliberately walks types only, under its
"Proofs may use anything" license), and the walk STOPS at the
boundary-module whitelist instead of an Iris/relation forbidden set.

## The gap this closes (why neither existing defense catches a veneer)

- The Audit statement-TCB gate polices STATEMENT closures only — its own
  docstring license: "Proofs may use anything" (`proofs/Audit.lean:136`).
- Cost profiles cannot discriminate at corpus scale: kernel grinding is
  CHEAP on 15–60-line programs — a veneer is a cost INLIER (plan §2d).
- Negative twins don't either: a veneer proves a twin as easily as the
  positive.

## Design ([AGENT] decisions, 2026-08-28)

**Scope mechanism** — one tracked config, `scripts/wp-lint-scope.txt`,
consumed by BOTH halves of the gate:

- `police <path>` / `police-dir <dir>`: files ABOVE the boundary (tier-3
  WP proofs). Corpus files ADD THEMSELVES here as they land.
- `boundary <path>` / `boundary-dir <dir>`: the Laws/lifting/adequacy
  layer itself — the sanctioned machine crossing. Exempt from the
  machine-mention rules (that layer's job IS mentioning the machine);
  kernel-decision bans still apply.
- `boundary-kernel-ok <path>`: boundary file carrying §2d-GRANDFATHERED
  `decide +kernel` certificates (today exactly one: `LangD.lean`'s
  spawnNoop pilot pair — the plan's "existing pilot quartets are
  grandfathered as labeled scaffolding" clause; retirement condition
  recorded there). `native_decide` stays banned. New files never start
  here.
- `exempt <FQName>`: per-theorem carve-out for the closure check (plan
  §6.3's declared-carve-out clause — sanctioned ∃-discharge sites), with
  provenance comments; a non-resolving entry FAILS. Empty today.
- Everything unlisted is out of scope: below the boundary (GoCore,
  language-instance machinery, ghost state) or pre-Iris-era modules
  policed by their own gates.

**Boundary classification** ([AGENT], from reading the tree): policed
seed = `proofs/GoLeanProofs/PinAdoptions.lean` (pure Iris-tier adoption
witnesses — above the boundary). Boundary = `Lifting.lean`,
`Adequacy.lean`, `TotalWp.lean` (its own header: "total lifting for our
prim steps" — it IS the total-lifting layer, so boundary rather than the
brief's suggested police seat), `Lang.lean`, `LangD.lean` (kernel-ok,
above), `LangC.lean`, `RunGlue.lean` (the plan's ∃-fuel "classification
glue"), and the `Laws/` tree (dir form — new Laws files join
automatically). Verified at seeding: no boundary file except LangD
contains `decide +kernel` or `native_decide`; no Laws/lifting/adequacy
file textually mentions the four executable names in code (TotalWp's two
mentions are docstring prose; comment-stripping keeps prose inert).

**Day-one text lint** — `scripts/wp-veneer-lint` (ci step 1e, static
section, blocking). Rules over comment-stripped source: V1
`native_decide`; V2 `decide +kernel`; V3 (police files only) machine
names (`stepFn`/`stepFnIter`/`execStmt`/`execStmtLoop`/`allStreamsOk`/
`allStreamsOkPool`) in unfold-class positions — `unfold`/`delta`
arguments, simp-family/`rw` bracket lists (multi-line,
bracket-balanced), equation-lemma references (`.eq_def`-class). BARE
mentions deliberately not banned: a corpus file's exported first-order
sentence may STATE the machine (the Audit gate's beat); it may never
UNFOLD it. Fail-closed: missing/unreadable config exit 2, EMPTY police
list exit 2, scope-listed file unreadable/missing exit 1, `*-dir` with
no `.lean` files exit 1.

**Proof-side closure check** — `scripts/WpVeneerClosure.lean` (ci step
3b0, after the proofs build, blocking). For every theorem declared in a
policed module: (a) statement precheck — the TYPE closure must not reach
the machine (first-order machine sentences belong in boundary-listed
export modules or on the exempt list; V-STMT names the chain); (b) the
proof-term walk — the VALUE closure, recursing through GoLean-rooted
constants' types AND values (theorems included — the re-aim), stopping
at boundary modules (the sanctioned route) and at non-GoLean upstream
(cannot reach our machine), fails on any machine constant reached
(V-PROOF, with the dependency chain). Kernel decisions on machine props
are caught by the same rule (the decided proposition carries the machine
constants into the term). Fail-closed: policed module absent from the
loaded env, zero scope theorems, non-resolving exempt/forbidden roots,
exhausted walk budget — all fail. Sited as a standalone scripts/ file
elaborated against the built oleans (NOT a proofs/ module): keeps
`proofs/Audit.lean`, the lakefile, and Challenge's trusted closure
untouched, so ci's existing steps and the judge-watched file set are
unmodified.

**Trust posture**: both steps are GATE ADDITIONS (strengthens-only); no
existing ci step was modified; `proofs/Audit.lean` untouched; no
designated-statement or trusted-closure movement ⇒ no comparator
landmark triggered by this unit (reported in the ci step comment too).

## Worktree bootstrap note ([AGENT], 2026-08-28)

This lane's `proofs/.lake/packages` predated the U0 iris pin move
(`8155e570`): iris absent, batteries/Qq at pre-move revs (lake deleted
the stale batteries on its failed network re-fetch — sandbox denies
network, by design). Populated OFFLINE at the tracked manifest pins,
setup-deps-style local clones: iris from this worktree's own
`deps/iris-lean` (which contains `e7a0a438…`), batteries/Qq from the
sibling checkout's packages (read-only source). Verified:
`scripts/setup-deps --only lake` reports all three `ok` at the manifest
revs. No network, no global state, sibling untouched.

## Fire-drill evidence (deliverable 4 — a tripwire that has never tripped is unverified)

### Text lint: clean-tree run

```
$ ./scripts/wp-veneer-lint; echo "exit=$?"
wp-veneer-lint: clean — 1 policed file(s), 18 boundary file(s), 0 violations
exit=0
```

(First honest catch, before the grandfather directive existed: the lint
red-flagged `LangD.lean:1100/:1120` — the spawnNoop `decide +kernel`
pair — proving V2 live against REAL tree content; resolved by the
`boundary-kernel-ok` grandfather entry per §2d's clause, not by
weakening the rule.)

### Text lint: the fire (scratch file, every banned shape; then removed)

Scratch `artifacts/atrip-demo/VeneerScratch.lean` (gitignored, deleted
after the drill) exercised V1, V2, V3-unfold, V3-simp (single and
multi-line bracket), V3-eq-lemma, plus two MUST-NOT-FIRE controls (a
bare statement mention; a comment mention). Run with the demo scope via
`GOLEAN_WP_SCOPE` (demo-only override; ci always runs the default):

```
$ GOLEAN_WP_SCOPE=artifacts/atrip-demo/scope-demo.txt ./scripts/wp-veneer-lint; echo "exit=$?"
wp-veneer-lint: VENEER-BAN VIOLATIONS (plan §2d — reformulate through the Laws/lifting/adequacy layer; a file that IS that layer moves to the config's boundary class with a reviewed reason):
  artifacts/atrip-demo/VeneerScratch.lean:5: V1 native_decide in WP-tier scope
  artifacts/atrip-demo/VeneerScratch.lean:8: V2 `decide +kernel` kernel-replay closure in WP-tier scope
  artifacts/atrip-demo/VeneerScratch.lean:11: V3 `unfold … stepFn` — direct machine unfold above the Laws/lifting/adequacy boundary (plan §2d)
  artifacts/atrip-demo/VeneerScratch.lean:15: V3 simp/rw set names `stepFnIter` — direct machine unfold above the Laws/lifting/adequacy boundary (plan §2d)
  artifacts/atrip-demo/VeneerScratch.lean:19: V3 simp/rw set names `allStreamsOk` — direct machine unfold above the Laws/lifting/adequacy boundary (plan §2d)
  artifacts/atrip-demo/VeneerScratch.lean:23: V3 simp/rw set names `stepFn` — direct machine unfold above the Laws/lifting/adequacy boundary (plan §2d)
  artifacts/atrip-demo/VeneerScratch.lean:23: V3 equation-lemma reference `stepFn.eq_def` — machine unfolding by equation lemma (plan §2d)
exit=1
```

Both controls stayed silent, as designed.

### Text lint: fail-closed drills

```
$ GOLEAN_WP_SCOPE=artifacts/atrip-demo/scope-empty.txt ./scripts/wp-veneer-lint; echo "exit=$?"
wp-veneer-lint: FAIL — scope config 'artifacts/atrip-demo/scope-empty.txt' lists NO police files (an empty tripwire scope is a misconfiguration, never a pass)
exit=2
$ GOLEAN_WP_SCOPE=artifacts/atrip-demo/scope-missing.txt ./scripts/wp-veneer-lint; echo "exit=$?"
wp-veneer-lint: scope problems (fail closed):
  artifacts/atrip-demo/NoSuchFile.lean: UNREADABLE ([Errno 2] No such file or directory: 'artifacts/atrip-demo/NoSuchFile.lean') — a scope-listed file must be scannable (fail closed)
exit=1
$ GOLEAN_WP_SCOPE=artifacts/atrip-demo/nonexistent-config.txt ./scripts/wp-veneer-lint; echo "exit=$?"
wp-veneer-lint: FAIL — scope config 'artifacts/atrip-demo/nonexistent-config.txt' missing or unreadable (fail closed)
exit=2
```

### Closure check: clean-tree run

```
$ cd proofs && GOLEAN_MEM_MAX=48G ../scripts/capped lake env lean ../scripts/WpVeneerClosure.lean; echo "exit=$?"
wp-veneer-closure: 2 policed theorem(s) across 1 module(s), all proof terms reach the machine only through the 18 boundary module(s); 0 exempt
  GoLean.Iris.pointsTo_fraction_agree: 255 statement / 299 proof constants walked
  GoLean.Iris.pointsTo_fraction_recombine: 255 statement / 297 proof constants walked
exit=0
```

### Closure check: the fire (scratch module, then removed)

Scratch `proofs/VeneerScratch.lean` (temporary; olean built by hand for
the drill; both deleted after): five theorems — a V-PROOF fire
(machine-free statement, proof term touches `stepFn`), a V-STMT fire
(statement speaks `stepFnIter`), a boundary-route CONTROL (cites
`GoLean.Iris.go_adequacy` — must pass), a grinding helper, and a
transitive fire that cites only the innocent-looking helper. Demo driver
= the checker with one added `import VeneerScratch`
(`artifacts/atrip-demo/WpVeneerClosureDemo.lean`, gitignored); demo
scope via `GOLEAN_WP_SCOPE`. Verbatim:

```
$ GOLEAN_WP_SCOPE=../artifacts/atrip-demo/scope-closure-demo.txt GOLEAN_MEM_MAX=48G \
    ../scripts/capped lake env lean ../artifacts/atrip-demo/WpVeneerClosureDemo.lean; echo "exit=$?"
../artifacts/atrip-demo/WpVeneerClosureDemo.lean:69:0: error: wp-veneer-closure FAILED — the veneer tripwire (docs/2026-08-28_iris-corpus-plan.md §2d; scope: scripts/wp-lint-scope.txt):
  VeneerScratchNS.veneer_proof_fire [V-PROOF]: proof term reaches machine constant GoLean.GoCore.Machine.stepFn OUTSIDE the Laws/lifting/adequacy boundary — the VENEER (plan §2d); route through the boundary layer
    chain: VeneerScratchNS.veneer_proof_fire → GoLean.GoCore.Machine.stepFn
  VeneerScratchNS.veneer_stmt_fire [V-STMT]: STATEMENT reaches machine constant GoLean.GoCore.Machine.stepFnIter — a first-order machine sentence does not live in a policed corpus module; move it to a boundary-listed export module or the exempt list (with provenance)
    chain: VeneerScratchNS.veneer_stmt_fire → GoLean.GoCore.Machine.stepFnIter
  VeneerScratchNS.veneer_stmt_fire [V-PROOF]: proof term reaches machine constant GoLean.GoCore.Machine.stepFnIter OUTSIDE the Laws/lifting/adequacy boundary — the VENEER (plan §2d); route through the boundary layer
    chain: VeneerScratchNS.veneer_stmt_fire → GoLean.GoCore.Machine.stepFnIter
  veneer_helper [V-PROOF]: proof term reaches machine constant GoLean.GoCore.Machine.execStmt OUTSIDE the Laws/lifting/adequacy boundary — the VENEER (plan §2d); route through the boundary layer
    chain: veneer_helper → GoLean.GoCore.Machine.execStmt
  veneer_transitive_fire [V-PROOF]: proof term reaches machine constant GoLean.GoCore.Machine.execStmt OUTSIDE the Laws/lifting/adequacy boundary — the VENEER (plan §2d); route through the boundary layer
    chain: veneer_transitive_fire → veneer_helper → GoLean.GoCore.Machine.execStmt
exit=1
```

The boundary-route control (`veneer_boundary_ok`) is correctly ABSENT
from the violation list, and PinAdoptions' two theorems pass alongside.

**Found live at this drill and fixed** ([AGENT]): the first checker
version's upstream filter ("module root not `GoLean*` → stop") silently
skipped the scratch module's own helper lemmas because the scratch
module name was not GoLean-rooted — the transitive fire did NOT fire. A
fail-open corner: fixed by recursing into POLICED modules
unconditionally, before the upstream filter; the transitive fire above
is the post-fix evidence (full chain reported).

### Closure check: scope-rot fail-closed drill

A policed file that exists on disk but is not built into the audited
environment (the config-rot case: a corpus file listed but never
imported) must FAIL, never silently scan nothing:

```
$ GOLEAN_WP_SCOPE=../artifacts/atrip-demo/scope-rot.txt GOLEAN_MEM_MAX=48G \
    ../scripts/capped lake env lean ../scripts/WpVeneerClosure.lean 2>&1 | tail -1
../scripts/WpVeneerClosure.lean:68:0: error: wp-veneer-closure: policed module SliceSpike ('proofs/SliceSpike.lean') is NOT in the loaded environment — a policed file must be built into the audited import closure (fail closed; import it from the GoLeanProofs root)
```

## Status

- Day-one text lint: **LANDED** (ci step 1e, blocking).
- Proof-side closure check: **LANDED** (ci step 3b0, blocking) — not
  parked; the walker re-aim fit the session.
- CLAUDE.md: one pointer line added at the stack section's veneer-ban
  paragraph naming the two checkers + scope config.
- Comparator landmark: **not triggered** — `proofs/Audit.lean`,
  `Challenge.lean`, the lakefile and the designated set are all
  untouched; the checker is a standalone `scripts/` file outside
  Challenge's trusted closure. (Reported in ci step 3b0's comment too.)

## Gate ceremony ([AGENT], 2026-08-28)

Full `scripts/ci --diff` under the box-wide build lock
(`artifacts/build-lock.d`, taken and released this run), 48G cap
(`GOLEAN_MEM_MAX=48G` → `LEAN_NUM_THREADS=6`), on the tree carrying
exactly this unit's changes (`CLAUDE.md`, `scripts/ci`,
`scripts/wp-veneer-lint`, `scripts/wp-lint-scope.txt`,
`scripts/WpVeneerClosure.lean`, this log): **RESULT: PASS, exit 0** —
all 29 ok, zero FAIL. Both new steps ran green in-build:

```
  ok   WP veneer text lint (no kernel-decision/machine-unfold in WP-tier scope)
  ok   WP veneer proof-closure (proof terms reach the machine only through the boundary layer)
```

plus `baseline diff FULL (2475/2475, no regression)`, `negative
baseline diff (no regression)`, `eval tests (141 ok)`, escape-hatch/
surface-purity/statement-TCB all ok. `--diff` was run (this lane
worktree had no recorded differential; the record is now fresh at this
tip) — not because runtime code changed: it did not. Comparator
landmark: NOT owed — the summary carries no scope note and no
staleness note (last certified run 51 theorems / 118 s @ 534f27109180,
1 commit behind); this unit touches neither `Audit.lean` nor
Challenge's closure. Full log: `artifacts/atrip-demo/ci-full.log`
(gitignored, local).

Reproducing the failure demos: appendix below carries both scratch
files verbatim plus the demo-scope recipes; with the `GOLEAN_WP_SCOPE`
override and (for the closure drill) the one-line sed adding
`import VeneerScratch` to a copy of the checker, every drill is
reconstructible from this log alone.

## Appendix — the drill scratches, verbatim

Lint drill `artifacts/atrip-demo/VeneerScratch.lean` (scope:
`police <that file>` + one boundary entry):

```lean
-- A-TRIP fire drill scratch: every banned shape, one file. NEVER LANDS.
import GoLean.GoCore.MachineSound

theorem scratch_v1 : True := by
  native_decide

theorem scratch_v2 : True := by
  decide +kernel

theorem scratch_v3_unfold : True := by
  unfold GoLean.GoCore.Machine.stepFn
  trivial

theorem scratch_v3_simp : True := by
  simp only [GoLean.GoCore.Machine.stepFnIter,
             GoLean.GoCore.Machine.execStmt]

theorem scratch_v3_multiline : True := by
  simp [Nat.add,
        GoLean.GoCore.Machine.allStreamsOk]

theorem scratch_v3_eqlemma : True := by
  rw [GoLean.GoCore.Machine.stepFn.eq_def]

-- a BARE statement mention (must NOT fire — statements may speak the machine):
theorem scratch_ok_bare : GoLean.GoCore.Machine.stepFnIter = GoLean.GoCore.Machine.stepFnIter := rfl

-- a prose mention in a comment: stepFn unfold simp [stepFn] (must NOT fire)
```

(The lint drill never needs to elaborate — it is a text scan; the file
above deliberately contains theorems that would not all elaborate.)

Closure drill `proofs/VeneerScratch.lean` (elaborated to an olean by
`lake env lean -o .lake/build/lib/lean/VeneerScratch.olean`, scope:
`police proofs/VeneerScratch.lean` + `police PinAdoptions` + boundary
Adequacy/Lifting/Lang/Laws):

```lean
-- A-TRIP closure-check fire drill scratch. NEVER LANDS; deleted after the drill.
import GoLean.GoCore.MachineSound
import GoLeanProofs.Adequacy

namespace VeneerScratchNS

/-- V-PROOF fire: machine-free statement, proof term touches the machine. -/
theorem veneer_proof_fire : True := by
  have _ := @GoLean.GoCore.Machine.stepFn
  trivial

/-- V-STMT fire: the statement itself reaches the machine. -/
theorem veneer_stmt_fire :
    GoLean.GoCore.Machine.stepFnIter = GoLean.GoCore.Machine.stepFnIter := rfl

/-- Control (must PASS): the machine reached only THROUGH a boundary module. -/
theorem veneer_boundary_ok : True := by
  have _ := @GoLean.Iris.go_adequacy
  trivial

end VeneerScratchNS

/-- The hidden helper: ITS proof grinds the machine. -/
theorem veneer_helper : True := by
  have _ := @GoLean.GoCore.Machine.execStmt
  trivial

/-- V-PROOF transitive fire: cites only the innocent-looking helper. -/
theorem veneer_transitive_fire : True := veneer_helper
```
