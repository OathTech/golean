# The WP-walk driver, exemplar-first (spec-parity slice 3, 2026-08-10)

Charter item 3 (`docs/2026-08-09_spec-parity-arc-charter.md`). Branch
`spec-parity-s3` off `spec-parity` @ 419010af. This note opens with the
exemplar's design (the spec shape it fixes), then the driver design
(what the tactic does and does NOT claim), then the scaling manifest.
The parking ledger (user-scale items, AFK posture) closes it.

## 1. The exemplar: `testCompareNilToNil` (imported-goose semantics/nil)

**Chosen program**: the imported oracle `testCompareNilToNil` from
`Corpus/coverage/exec/imported-goose/semantics/nil/` (upstream
`testdata/examples/semantics/nil.go` @ 3be88bbb; body verbatim). Why
this one:

- **It is in THEIR proved set.** Perennial proves
  `wp_testCompareNilToNil` as a `test_fun_ok` lemma
  (`deps/perennial/new/proof/.../semantics_proof/nil.v` @ 43d4efab) —
  one of the 37 proved oracles the charter's parity claim is measured
  against. The exemplar is therefore a real parity row, not merely a
  same-class stand-in.
- **It is R1-green and R2-pinned on our side** — the differential row
  passes against `go run`, and the staleness-guarded lowering term
  `nilLowered` (`proofs/GoLeanProofs/Specs/ImportedGooseNil.lean`,
  ci step 1c5) already exists, so the R3 statement quantifies the
  frontend's ACTUAL lowering, not a hand-transcription.
- **Its body exercises the spine widely but finitely**: declaration at
  a pointer type, `new(*uint64)` (the allocating wide-op class), an
  assignment, a deref-read, a nil comparison, return — plus the
  `golean*` wrapper's call / frame-exit / if / literal-assign
  machinery shared by every oracle in the class.

**The feature class the exemplar fixes**: goose `test_fun_ok`-style
sequential boolean oracles under the imported-goose wrapper convention
— `golean<TestName>()` calls the verbatim `test<Name>() bool`, maps
`true` to the int `1`, and the driver statement
`.call #[.var "r"] ⟨"golean<TestName>"⟩ #[]` writes the verdict into
the harness cell at base address 0 (the TotalPins observable
convention, seed `heap = [cell 0 ↦ int 0]`, `nextAddr = 1`).

**The spec shape (D1: BOTH, per the goldenSpecC/goldenReturnsTwoC
precedent)** — for each proved oracle, two theorems:

1. **The designated-shape triple** — `GoSpecC` (the concurrent-carrier
   full surface judgment, sequential-degenerate lane) at FULL
   `InitialSplit` strength:

   ```
   GoSpecC nilLowered.typeDefs.toList nilLowered.funcs
     nilLowered.methods nilEnv (r ↦ ⟨int, 0⟩) driver (r ↦ ⟨int, 1⟩)
   ```

   proven as `goSpecC_of_goSpec (goSpec_of_wp <the hand walk>)` — the
   per-program content is exactly the WP walk through the laws spine;
   the frame quantifier, safety half, and pool transfer are the
   once-proven pipes. The postcondition `r ↦ 1` is the oracle's TRUE
   verdict — the same value the differential row pins against
   `go run`, and strictly stronger than their `test_fun_ok` (partial
   correctness on an untested model, no termination): ours adds
   interpreter-side safety (`ProgressExecC` — no deadlock, no race
   refusal, no stuck state on any modeled schedule) over the
   differentially tested machine.

2. **The first-order readout twin** — on the SAME carrier as the
   judgment (the goldenReturnsTwoC precedent):

   ```
   ∀ fuel ch σf ch', execProg fuel nilEnv nilOut ch driver
     = .ok (.normal σf, ch') → loadLoc σf (.base ⟨0⟩) = .ok (.int 1 .int)
   ```

   readable from base interpreter definitions alone (deletion test:
   no Iris, no relation, no tactic machinery in the statement).

Both are stated over the seeded TotalPins convention so they compose
with the existing R2 pins (`Terminates` + canonical readout): for a
proved oracle the R2 termination pin plus the R3 spec's safety half
yields `TerminatesNormally` — the pieces are stated to snap together,
not as disconnected artifacts.

**Non-vacuity**: the exemplar IS a discharge witness (a concrete
program with every premise discharged — the readout twin instantiates
`InitialSplit` at the concrete seed with `wf` by `decide +kernel`).
Axiom budget: `propext, Classical.choice, Quot.sound` (the standing
proofs-package budget; checked by the in-build Audit sweep).

**What stays sequential-degenerate, stated honestly**: `GoSpecC` here
is obtained by the conservation transfer (`goSpecC_of_goSpec`) — these
programs spawn nothing, so the pool run IS the sequential run
(`execProg_single_eq_execStmt`). The genuinely-spawning
frame-quantified `GoSpecC` remains slice 4's work; nothing here claims
it.

## 2. The wrapper/driver kit (shared, per-convention, not per-program)

Every oracle in the class shares the wrapper shape modulo three
parameters (the gensym target name `$cN`, the inner `FuncId`, the
wrapper `FuncId`). `Specs/GooseParityKit.lean` factors that:

- `goleanWrapperBody cname innerFid : Stmt` — the wrapper body as a
  function of the two names; per-unit an `example : … = by rfl` pins
  that the IMPORTED lowering's wrapper body is literally this term
  (if the frontend's wrapper generation drifts, the pin — and the
  staleness guard 1c5 before it — fails loud).
- `wp_golean_wrapper_body` — the wrapper walk, parameterized by the
  inner function's body spec (a wand delivering `$res0 ↦ .bool true`);
  covers init `$cN`, the inner call's frame entry/exit
  (`wp_call_enter_ret1` / `wp_frame_return₁` at a bool cell), the
  `if $cN` branch, `$res0 = 1`, return.
- `wp_golean_driver` — the driver statement's walk into the wrapper,
  ending `{r ↦ 0} … {r ↦ 1}` in the exit-form WP `goSpec_of_wp`
  consumes.
- `goSpec_seeded_readout` / `goSpec_seeded_readoutC` — the generic
  readout-twin derivations: a sequential `GoSpec` at the TotalPins seed
  yields the first-order readout on the sequential and pool carriers
  (the goldenReturnsTwo/goldenReturnsTwoC derivations, proven once
  instead of per-program).

The kit is CONVENTION-specific (imported-goose wrapper/seed shapes),
so it lives in `Specs/`, not in a general law module (layering
doctrine: general modules never encode target/corpus conventions).

## 3. The driver (`go_walk`) — what this slice adds, and what the tactic does not claim

The tactic core `go_walk` (proofs/GoLeanProofs/Tactics/GoWalk.lean)
exists since the proof-automation arc: a `DiscrTree` of
`@[go_walk_law]`-registered spine laws, most-specific-first, each step
fully backtracked, side conditions closed only by
`rfl`/`assumption`/`go_walk_simp`+`decide`/`omega` — a real semantic
obligation stops the walk instead of being guessed at. THIS SLICE DOES
NOT REWRITE IT. What this slice adds is coverage and the exemplar-first
usage pattern for the imported class:

- registered spine laws where the class needs them and the law is
  genuinely mechanical (per-law below);
- the kit lemmas of §2, so the per-program side-goal surface is the
  INNER body walk only;
- the scaling manifest (§4) with per-program disposition.

**Where the walk stops, by design** (the side-goal surface — supplied
with `go_walk_step law` and proven by hand at each site):

- allocating wide ops (`new`/`make` — `wp_stmt_op_apply_alloc_store`
  instances: the transition fact `happly` is a semantic obligation);
- store steps at non-int cells (`wp_assign_store`'s `hstore`);
- frame entries (`wp_call_enter_*`: `hfind` needs the program pin
  `GoCoreGS.prog GF = …`, which is a hypothesis of the surrounding
  walk, never global state);
- strict-op applications whose result the goal does not determine
  (`wp_strict_apply_pure/pin`'s `out` + `happly`);
- anything nondeterministic, invariant-carrying, or unregistered.

**THE TACTIC IS NEVER TRUSTED.** Every proof it produces elaborates to
a kernel-checked term; the in-build Audit gate pins the axiom set
(`propext, Classical.choice, Quot.sound` — no `native_decide`, no
`sorry`); the statements it proves are stated in Surface vocabulary
over the interpreter and pass the deletion test (Iris and the tactic
appear only in proofs). A `go_walk` bug can make a proof FAIL, never
make a false statement PROVABLE.

**Phase-2 outcome (the exemplar re-derived tactic-driven).**
`wp_compareNil_body`'s proof is now the `go_walk` walk — statement
byte-identical; the hand walk is preserved in full as
`wp_compareNil_body_hand` (the walk-architecture witness, and the
proof-robustness fallback). The realized side-goal surface for this
body, exactly as designed: the two pointer declarations
(`wp_init_ptr` — `hdef` is `∀σ` under the type pin), the
`defaultValue` nullary eval (same `∀σ` shape), the `new` alloc-store
(`wp_new_value`), the two pointer/bool cell stores
(`wp_assign_store`), and the comparison's apply
(`wp_strict_apply_pure` — `out` undetermined by the goal). Everything
else — 60+ machine steps — is the table.

**Registration lesson (recorded the hard way):** registering
`wp_init_bool`/`wp_init_ptr` as `@[go_walk_law]` moved the STOPPING
POINTS of the standing quorum walks (their `go_walk_step (wp_init …)`
supplies then faced already-advanced goals and timed out). The law
table is a GLOBAL tactic surface: a new registration changes every
existing walk script's behavior. Policy adopted: new laws default to
UNREGISTERED (supplied via `go_walk_step`); a registration is its own
deliberate change validated against every walk consumer. The two init
lemmas ship unregistered with this note recorded in their docstrings.

## 4. Scaling manifest

Moved to `docs/spec-parity-r3-manifest.md` (tracked; per-program
disposition — proved / side-goals-remaining / out-of-class /
not-attempted — over the imported sequential-oracle class). A program
the driver cannot finish is a VISIBLE row there, never a silent skip.

## 5. Designation candidates (D3 is CURATED — user sign-off at arc end)

Nothing is designated in this slice; `proofs/Audit.lean`'s list and the
44 designated statement files are byte-identical. CANDIDATES recorded
for the arc-end curation (one exemplar per feature class):

- `GoLean.ImportedGoose.SemanticsNil.compareNilToNilSpecC` (the
  designated-shape triple, §1 form 1);
- `GoLean.ImportedGoose.SemanticsNil.compareNilToNilReadoutC` (the
  first-order readout twin, §1 form 2).

The bulk R3 instances are gate-checked (axiom-pinned by the in-build
Audit module sweep, statement-TCB-clean by construction — stated in
Surface/interpreter vocabulary) but undesignated, listed in the
manifest.

## 6. Parking ledger (user-scale items; AFK posture)

- **P-S3-1 — (placeholder; filled as items arise.)**

## 7. Build log

- (appended per movement)
