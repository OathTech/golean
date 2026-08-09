# Gobra as a Lean-backed proof language — feasibility study + spike (2026-08-09)

**Status:** exploratory; worktree `gobra-contracts` (branch
`worktree-gobra-contracts` off `main` @ `3d215822`), isolated from the
main-line build. Sibling study to `docs/2026-08-09_verdi-compat-layer.md`
(the verdi-compat worktree), same operating pattern.

**The question (user prompt):** golean began with Gobra as its frontend;
now that the project is mature, could we support Gobra *contracts* and
verify them in Lean — ideal end state: Gobra becomes a Lean-backed proof
language, with golean as the verification layer?

**Answer in one line:** yes, and the pieces fit unusually well — Gobra's
annotation kit (`requires`/`ensures`/`invariant`/`decreases`) supplies
*exactly* the inputs golean's `go_walk` automation cannot infer, the
contract surface compiles naturally onto the existing Iris-free Surface
layer (`GoFuncSpec`/`GoSpecT`), the spike already carries the Gobra
tutorial's first example end-to-end (annotated canonical Go → frontend →
pinned lowering → contract as a Lean statement → kernel-checked seed
witnesses), and the niche is wide open: nobody has given any Viper
front-end an ITP backend, and Gobra's own authors state in writing that
its translation soundness is unproved. The honest hard parts: an
automation engine of RefinedC/Lithium class does not exist in Lean and
would have to be built (golean's `go_walk` + law table is the seed), and
every contract construct needs a statement-adequacy argument — the spike
surfaced two divergences (unbounded-vs-machine ints, division
convention) on the very first example.

---

## 1. What Gobra is, and the contract surface (report A)

Gobra (viperproject/gobra @ `36e39e3`, cloned at `deps/gobra`): the
Viper-based Go verifier. Pipeline: ANTLR4 parse (the spec grammar is
~110 lexer + ~520 parser lines *extending stock Go*) → typecheck →
desugar to a typed internal IR (`ast/internal/Program.scala`, ~332 node
kinds, ghost-elaborated, source-tracked, **no serializer today** — only
a pretty-printer) → per-concept Viper encodings → Silicon/Carbon → Z3.

Contract vocabulary, layered by semantic commitment:
- **Pure-value layer**: `requires`/`ensures`/`preserves`, loop
  `invariant`, `decreases` (tuple measures, conditional), `pure`
  functions (single-expression, must terminate), `old()`/labeled old,
  quantifiers with Viper-style triggers, math types (`seq`/`set`/
  `mset`/`dict`/`option`/`adt`/`domain`+axioms).
- **Heap layer**: `acc(e[, p])` accessibility with fractional/wildcard
  permissions (implicit dynamic frames; `&&` is separating), quantified
  permissions (the slice idiom), `x@` addressability, predicates with
  `fold`/`unfold`, magic wands.
- **Structuring layer**: interface specs + behavioral-subtyping
  implementation proofs, closure specs, ghost code (members/statements/
  params/fields/types, `assert by`/`assume`/`inhale`/`exhale`).
- **Concurrency layer**: `go f()` = exhale pre (postcondition
  discarded); `sync.Mutex` lock invariants as first-class predicates
  (trusted stubs); channel invariants (`Init(sendInv, ackInv)`);
  package invariants; `atomic`.

Attachment modes: native `.gobra` files, OR ordinary `.go` with
`//@`/`/*@ @*/` comments (the `Gobrafier` preprocessor — regex-based,
itself a trust wart on their side); spec-only header files for
libraries; `trusted` and bodiless members are assumed.

Their trust story: Scala frontend+encoder (~30k lines) + Viper +
Silicon/Carbon(+Boogie) + Z3 + stubs, all trusted; **no certification
anywhere in the repo**, and soundness-relevant flags default loose
(`assumeInjectivityOnInhale`). Gaps for parity claims: no generics, no
`recover` (panic is specced `requires false`), limited strings/floats.

## 2. The golean Gobra era, and what survives (report B)

Gobra WAS the frontend until 2026-07-18 (`e82021e7` removed it; decision
record `docs/2026-07-18_prioritization.md` — coverage: only ~136/672
corpus cases reached Lean; Gobra rejects legal Go; per-fixture SBT
export; single-file packages). What was consumed then was the *typed
internal IR* serialized by our own fork (septract/gobra-json), decoded
fail-closed in Lean with **Lean as schema authority**.

Survivals relevant now:
- **Recoverable at `git show e82021e7^:GoLean/GobraJson.lean`** (1,251
  lines): typed Lean decoders for Gobra's SPEC constructs — assertions
  (`access`+`Permission`, `sepAnd`, implication), pres/posts/termination
  measures, `Old`, predicates, ghost flags, `while` with invariants.
  The assertion-language *model* is a design reference even though the
  wire it decoded is gone.
- **Live idioms descended from that era**: the frontend-independent
  corpus, `TypeId`/`FuncId` + one-boundary mangling rule, StrictJson
  fail-closed decoding, "GoCore stays pure" (spec constructs were kept
  out of GoCore even then — `4047695c`).
- **The current spec surface is contract-shaped already**:
  `GoFuncSpec` (function-level: pre-heap + args → result satisfying Q;
  v1 unary-int), `GoSpecT` (total correctness = triple + safety +
  termination — exactly `requires`/`ensures` + `decreases`),
  encoding predicates (`EncodesConfig`/`EncodesAcked`) as the worked
  idiom for typed pre/posts over heap snapshots, `goSpec_of_wp` as the
  Iris exit pipe, and the statement-TCB doctrine forcing contracts to
  compile to the Iris-free Surface layer (never Iris `WP` directly).
- **The frontend already parses comments** (`parser.ParseComments` on,
  never consumed) and the wire has a proven optional-key extension
  pattern — a `"specs"` key is the sanctioned mechanism, with spec
  nodes quarantined out of GoCore per the purity rule.
- **Automation state**: `go_walk` + ~54 registered WP laws; −73% tactic
  volume on the quorum walks; stops BY DESIGN at loop invariants,
  semantic witnesses, and resource splits. Largest fully-proved real
  function: ~45-line `CommittedIndex` at ∀-config generality.

**The load-bearing alignment:** `go_walk`'s designed gaps (loop
invariants, termination measures) are precisely what Gobra annotations
carry. The contract language is the missing input channel for the
automation we already have.

## 3. Prior art and the trust argument (report C)

- **The niche is open.** The entire Viper-detrusting effort (ETH "Viper
  Roots": Boogie proofgen CAV 2021, Viper→Boogie proofgen PLDI 2024,
  CoreIVL/ViperCore) is Isabelle-based, per-run translation-validation,
  covers subsets, and **stops at the Viper layer — every front-end
  encoding, Gobra's included, stays trusted**; ETH theses state Gobra's
  translation soundness is unproved. No Viper→Lean work exists at all.
- **Closest architectural analog: RefinedC** (+RefinedRust): comment
  annotations on unmodified source, obligations against an Iris-based
  system in Coq, foundational, automation-first (Lithium: goal-directed,
  no-backtracking SL proof search) with interactive escape, no SMT in
  TCB. Key transferable lesson: *rule format co-designed with the proof
  search engine*.
- **Workflow precedents**: the Dafny→Lean cluster (Lean-on-Dafny,
  Velvet) shows the "SMT-verifier surface, Lean underneath" workflow;
  Why3's ITP replay is the mature cautionary tale (drivers as soft
  underbelly, replay fragility); HOL-Boogie is the adequacy cautionary
  tale — **discharging obligations in an ITP buys nothing unless the
  obligation's meaning is defined in the ITP against a semantics of the
  source**. Our design passes that test by construction: contract
  meaning is defined once, in Lean, over GoCore.
- **The missing piece**: no Lithium-class SL automation exists in Lean 4
  (iris-lean ≈70% ported: proof mode, UPred/IProp, invariants — no
  obligation-discharge engine). Best Lean-native design pattern: Yolo
  (ITP 2026) — fast unverified prover + kernel-checked certificates.
- **Adequacy hard cases from ETH's own program**: real-vs-rational
  fractional permissions, counting-permission encodings, Viper-defined
  constructs (perm introspection, wands, QPs). Any construct whose Gobra
  meaning is "whatever the encoding does" needs a documented Lean
  meaning + optionally the Isabelle semantics as cross-check oracle.

## 4. The spike (done, builds clean)

`compat/gobra/` — a Lake package requiring `golean-proofs` by path
(transitively GoLean + iris-lean), referenced by nothing in the main
build (same isolation contract as `compat/verdi`). Contents:

| Artifact | What it demonstrates |
|---|---|
| `testdata/sum/main.go` | the Gobra tutorial `sum` as **valid canonical Go** with the full contract in `//@` clauses; passes `go vet`; corpus-style subjects + `cases.tsv` |
| `testdata/sum/wire.json`, `sum-lowered.repr` | the native frontend runs UNCHANGED on annotated source (annotations invisible); decode → 138-line repr |
| `GobraCompat/SumProgram.lean` | the pinned lowering (golden-pin convention; axiom-free) |
| `GobraCompat/Contract.lean` | a deep embedding of the ring-0 contract fragment (`GExpr`/`GAssertion`/`GobraContract`, decidable evaluation) + **the elaboration** `contractStatement` into `GoFuncSpec` — meaning defined once, over GoCore, Iris-free |
| `GobraCompat/Sum.lean` | `sumContract` (1:1 transcription incl. loop invariants + `decreases`), `SumContractStatement` (the named target Prop), and kernel-checked seed witnesses: machine runs at n=0/1/5/12 agree with the contract post; negative twin refutes a wrong result |
| `AxCheck.lean` (build-wired) | axiom audit: pin and contract axiom-free; the statement's axioms are the Surface layer's (`propext`/`Classical.choice`/`Quot.sound`) |

**Adequacy divergences surfaced by example #1** (deliberately visible in
the statement, not hidden):
1. **Unbounded vs machine ints.** Gobra's default `int` is mathematical
   (overflow checking opt-in via `--overflow`); GoCore's is int64. The
   elaboration takes an explicit `adequacyGuard` (for `sum`:
   `0 ≤ n ≤ 2^31`) confining the claim to where they agree. The guard
   is spec content — auditable, and exactly what Gobra's own
   `--overflow` mode would impose.
2. **Division convention.** Go truncates toward zero; Viper `div` is
   SMT-LIB-style. The fragment fixes Go/GoCore semantics (`Int.tdiv`);
   a full pipeline reconciles per construct (invisible on `sum`, where
   the dividend is always even and non-negative).

**Not done (the recorded next milestone):** the proof of
`SumContractStatement` — a `go_walk` WP walk where `wp_while_inv`'s
invariant is `sumContract.loopInvariants` instantiated over machine
state. This is the load-bearing item for the whole thesis ("annotations
feed the automation") and is deliberately statement-first per house
style. Sized by the quorum-pilot precedent (a small fraction of the
`CommittedIndex` walk).

## 5. Architecture options

- **A. Native annotation path (recommended).** The native frontend
  collects `//@` clauses (comments already parsed); clause TEXT goes on
  the wire under a `"specs"` key (raw strings + positions — the emitter
  stays a mechanical serializer per `wire.go` philosophy); a Lean-side
  parser + elaborator (authority in Lean, per the gobra-json-schema
  precedent) produces Surface statements; `go_walk`+successors
  discharge; failures drop into interactive Lean. Gobra-the-tool is not
  a dependency at all. Unsupported constructs fail closed at the
  elaborator.
- **B. Gobra-fork export path** (the old era revived): fork Gobra to
  serialize its typed internal AST with specs (the septract/gobra-json
  precedent + recoverable decoders). Buys Gobra's own
  typechecker/desugarer; costs the Scala/SBT dependency the project
  deliberately deleted, and couples us to their IR.
- **C. A + Gobra as differential oracle**: dual-run on the fragment
  both support — Gobra/Z3 verdict vs Lean discharge on the same
  annotated source. Not a soundness argument (both could be wrong), but
  a drift detector for spec MEANING, in the house differential
  tradition. Cheap once A exists; also the on-ramp for existing
  Gobra-annotated corpora (VerifiedSCION, WireGuard) as a test suite.

## 6. Scope rings (the downscope ladder)

- **Ring 0 (spike, done):** `requires`/`ensures`/`invariant`/
  `decreases` over ints; unary functions.
- **Ring 1:** the full pure-value fragment — bools/multiple args/
  multiple results (needs the owed `GoFuncSpec` widenings:
  multi-result, `(T, error)`, argEnv), `old()` on values, `pure`
  functions ↦ Lean defs (the `QuorumRefSpec` idiom), math types ↦
  Lean types. First milestone target: ring 1 + the `sum` WP walk.
- **Ring 2 (the real threshold):** heap contracts — `acc` on
  pointers/fields ↦ `HProp.pointsTo` footprints; quantified
  permissions over slices ↦ a systematic **encoding-predicate
  generator** per Go type (today: two hand-written exemplars);
  predicates ↦ named `HProp`s with `fold`/`unfold` definitional.
- **Ring 3:** interfaces/behavioral subtyping, closures specs.
- **Ring 4:** concurrency (mutex lock invariants ↦ Iris — note the
  in-flight mainline `sync` slice is the prerequisite and natural
  partner), channels ↦ our channel semantics + protocols; fractional
  permissions; magic wands; ghost code beyond pure.

## 7. The end state, honestly assessed

"Gobra becomes a Lean-backed proof language" = annotated Go in; golean
obligations out; automation discharges the walkable part; the residue is
interactive Lean **with goals kept close to the surface contract** (the
Frama-C lesson: an escape hatch usable only by Iris experts is not an
escape hatch); no Z3 in the TCB; Gobra-the-tool optionally cross-checks
(option C). Reachable in rings; the two long poles are (a) Lithium-class
automation in Lean (build on `go_walk`; adopt the Yolo
certificate-reconstruction pattern where search outgrows the law table)
and (b) the encoding-predicate generator for ring 2. Neither blocks
rings 0–1.

## 8. Decisions for the user (D1–D5)

- **D1 — architecture:** A (native, recommended) vs B (fork export) vs
  C-timing (when to stand up the differential oracle).
- **D2 — where the annotation parser lives:** Lean side (recommended:
  wire carries raw clause strings + positions; authority and failure
  modes concentrated in Lean) vs Go side (structured wire, bigger
  emitter).
- **D3 — syntax fidelity:** track Gobra's grammar exactly for the
  supported fragment (recommended: enables their test suite + existing
  annotated corpora as ours, fail closed elsewhere) vs a golean dialect.
- **D4 — first milestone:** ring 1 + the `sum` WP walk (recommended) vs
  going straight at a ring-2 heap example (`swap.gobra`).
- **D5 — home:** `compat/gobra` stays a standalone package until the
  wire `"specs"` key lands (that lands via a coordinated mainline
  slice, since it touches `tools/nativefrontend` + `NativeToIR` —
  parallel-lane coordination point per the verdi note §8b).

## 9. Artifacts

- This note; `compat/gobra/` (builds clean on `v4.31.0`, axiom audit
  build-wired); reference checkout `deps/gobra` @ `36e39e3`
  (clone-yourself, gitignored).
- Research reports (three agent runs, 2026-08-09) synthesized above;
  recoverable-era artifact index in §2.
