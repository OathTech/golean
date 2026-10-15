# Executed renderer correspondence — 2026-10-15

Checked implementation; final independent result review and immutable binding
are recorded below. No full-interface landing claim.

[USER] 2026-10-15: implement the bounded executed-renderer assignment from
`82353580814b66399cdc472a4c4edf9044d0c097`, retaining the independently
consumable observed-phase handoff `701d8689c1848394c2738134dcab0b6e4c7b50e5`.
The governing input is logic's
`docs/2026-10-15_relational-renderer-correspondence-charter.md` in the
`relational-demo-brief` tree. Preserve immutable acceptance inputs; no merge,
push, live repin, peer writes or global changes.

[AGENT] 2026-10-15: replace exactly the three demonstrated recursive derived
printers with transparent, structurally terminating definitions. Keep the
pinned toolchain's leaf printers and Format operations. Validate preservation
against the old generated bodies, with separate kernel and source arguments.
Worktree: `.claude/worktrees/relational-rendering-1015`, branch
`refactor/relational-rendering-1015`.

## Implemented account

`GoLean/GoCore/Rendering.lean` supplies constructor application, ordinary list,
array, pair and option Format combinators. `Ty.render`, `GoValue.render` and
`Expr.render` mutually recurse through their finite nested containers. The
existing `Repr` instances now directly use these total definitions. The six
public instance facts are `Ty.reprPrec_eq_render`, `Ty.repr_eq_render`, and
the corresponding `GoValue` and `Expr` facts. They are available through the
existing `GoLean.Relational` import; no consumer premise or downstream import
is added. Every precedence is covered, not just the ordinary zero/max uses.

No operational case, guard, choice, fuel test, store update, event, continuation,
error class or printing site changes. The mathematical reduction of formerly
opaque renderings does change: the kernel can now calculate their actual
Format trees. Rebuilding consumers against that change is required.

The checked experiment `experiments/2026-10-15-rendering/Derivation.lean`
contains nonrecursive, parameterized versions of the old generated bodies.
`ty_equation`, `govalue_equation` and `expr_equation` prove, for every finite
value and every precedence, that the new total renderer satisfies those exact
bodies when the recursive parameter is the new renderer. The container proofs
connect traversal to the pinned standard List/Array/Prod/Option renderers.
`SemanticLinks.lean` checks unrestricted representative links at `valueEq`,
`preprintDispatch`, `unseqAtom`, and `checkedDynamicTy`. In particular:

- `valueEq_bool_unit` retains the exact mismatched operand refusal for arbitrary
  context/right value.
- `preprint_unboxed` retains the internal-error text for every noninterface
  payload, context, store, member and panic flags.
- `unseq_nonatom` retains the exact refusal for every nonatom expression,
  context, environment and store.
- `dynamic_type_refusal` retains type rendering whenever the operation's
  `mentionsUnsupported` test is true, including nested function/container types.

The final exhaustive `valueEq` arm references Ty rendering; the compiled graph
includes it. This is a dependency overapproximation, not a reachability proof.
The sync arm has its own unsupported error and does **not** exercise that final
arm. No false sync-to-final-arm equation is retained.

## Preservation argument and its trust boundary

The old source is the immutable starting pin, not the candidate and not the
logical default behind an opaque declaration. Under Lean `v4.32.2`,
`Lean/Elab/Deriving/Repr.lean` generates the executed recursive bodies;
`Lean/Compiler/LCNF/ToDecl.lean` selects the `_unsafe_rec` implementation when
present. The old generated C and deriving traces were inspected in a private
archive/build. `check-derivation.py` checks the retained step bodies against
those traces, changing only binder decoration, whitespace and parameterizing
the recursive call. It accounts for every branch: 14 Ty, 15 GoValue, 59 Expr.

The source/derivation induction first establishes Ty, then GoValue and Expr
using the Ty result for their non-recursive type fields. Their recorded step
bodies use the candidate Ty instance; its equivalence to the old Ty instance
is supplied by that first source/derivation induction. Each induction is over
finite values and their nested containers. In a constructor, both algorithms use the same qualified name,
field order, `Format.line`, left-associated append, group, precedence-dependent
nest (one at max precedence, two below), and `Repr.addAppParen`, including
nullary constructors. Direct recursive arguments are rendered at max precedence.
Nested elements use precedence zero; an Option's present expression uses max
precedence. Ordinary non-atomic lists use `Format.bracket`; arrays use
`Format.bracketFill`, including their distinct empty forms. Pair order is
key then value. The checked container equations identify these operations with
the old local-instance calls. Inductive hypotheses apply to strict subvalues
and finite list tails. All leaf printers (including recursive Loc, byte-string
structures, identities, numeric kinds and primitive structures), escaping and
pretty layout operations are the same pinned toolchain/project definitions.
Thus the Format trees agree for every finite input/precedence under the old
executed recursive equations; applying the same layout yields the same text
at every width, indentation and column. No well-formedness restriction is used.

This is a separately reviewable source/derivation preservation argument, not a
kernel equality theorem to the former opaque constants. The kernel proves the
new account and its exact constructor/container equations. The pinned Lean
compiler/runtime remains trusted for the old executed bodies and for execution
of the new total definitions, as before. Matching controls alone would not
establish this universal preservation argument. There is no added axiom,
implementation override, native-decision shortcut or unsafe source definition.

Re-established compiled dependency closure, selected by defining module (so
private GoLean declarations are included): old `stepFn`/`stepMulti`/`runProgramM`
visit 2,244 / 2,487 / 2,335 project nodes and reach precisely the three opaque
renderer endpoints. New visits are 2,264 / 2,507 / 2,355, with no project opaque
endpoints in these three closures. The walk follows compiler-selected bodies,
including nested printer dependencies; toolchain definitions remain the trust
base. This is not an assertion that other project imports have no findings.

## Finding dispositions

The three affected declarations are individually addressed:

- `GoLean.GoCore.instReprTy.repr._unsafe_rec`: removed; actual instance uses
  total `Ty.render`, including nested function parameter/result lists.
- `GoLean.instReprGoValue.repr._unsafe_rec`: removed; actual instance uses
  total `GoValue.render`, including interfaces, struct field pairs, arrays
  and captured-value lists.
- `GoLean.GoCore.instReprExpr.repr._unsafe_rec`: removed; actual instance uses
  total `Expr.render`, including nested expression arrays, indexed array-literal
  pairs and optional slice maximums.

These are not renamed unresolved helpers: each new compiler-generated helper
has a transparent safe total kernel parent. Remaining implementation findings
stay failed and unwaived. The historical 16, frozen consumer 21, actual R2 47
and full-root 51 inventories have different import scopes; fresh corresponding
counts and exact set differences are recorded below.

Independent review identified a private-name exclusion in the initial closure
probe. Fixed by selecting defining modules; independent and author reruns
retain the same counts/endpoints. An earlier probe failed at missing `stepMulti`;
that failure was corrected by importing/building Multi and rerunning all roots.
Neither failed probe is used as all-driver evidence. Review also requested
explicit dependency order in the source argument (Ty before GoValue/Expr);
that order is now stated above, rather than treating the three equations as
independent equality to old implementations.

## Validation and immutable handoff

All builds/checks used `capped` and `LEAN_NUM_THREADS=2`. Full CI used the
chartered 64 GB cold-build cap and private Go/TMP caches. Reproduction is in
[the experiment README](../experiments/2026-10-15-rendering/README.md).

- Full `scripts/ci --diff`: **PASS**, 1,335 seconds; warning-free build of
  263 jobs, exact replay of all 114 GoLean source modules, exhaustive core axiom
  audit, all 396 evaluator tests, frontend/harness tests and boundary controls.
  Fresh differential results: 4,025 rows, 3,767 PASS / 258 tracked FAIL;
  no baseline regression. All 415 negative rows match. Scheduler whole-tape
  controls and all reported speedbumps pass. No baseline was edited.
- Renderer experiment: build **PASS120**; 13 headline instance/constructor/site
  statements use only `propext`. Exhaustive full-GoLean/experiment audit:
  **25,509 declarations**, standard axioms only. Exact replay **117 modules**
  (114 GoLean + three experiment modules), plus successful fresh replay of
  RendererAudit and its imports. Independent reviewer also elaborated/replayed
  the affected definitions and equations separately.
- All old/new controls match byte-for-byte (**9,821 output lines**). The same
  source runs against the immutable old and candidate Lake environments.
  The step control projects stores/tapes/labels/errors, not complete Configs;
  universal preservation rests on the source/derivation argument, not the
  finite sample. The full old generated-body comparison passes all 88 branches.
- Frozen observed-phase logic `3c9be98f8de86f04c4cec53d75490199718da066`:
  **PASS458**; direct PhaseAudit, 27,128-declaration exhaustive standard-axiom
  scan, all required proof-body edges, and exact **451-module replay**
  (114 GoLean + 131 local/adapters + 206 dependencies). All 137 original files
  excluding private Lake wiring, including 128 Lean sources, match their
  immutable objects. The actual guarded callee/caller and history/adequacy
  applications close with all three original laws supplied.
- Separate older joint O1/U1 consumer `5e8ed98ad68c31fa01ad879ed48b9ac8440ddb42`,
  materialized at reviewed handoff `eba7d3bdaa7786cfc6daad949cd3217185e2c867`:
  **PASS450**, original JointAudit and exact **443-module replay**
  (114 GoLean + 123 local/adapters + 206 dependencies). All 123 original files
  excluding private Lake wiring, including 115 Lean sources, match exactly.
- Latest completed R2 implementation
  `6da4e8aa25066fd26f7e81281a98c4133cf2dadb`, review `64f96bd`:
  **PASS461**, direct aggregate elaboration, 203 headlines and 6,649 local
  declarations with standard axioms; expanded actual/full-root exhaustive
  scans pass axioms for 30,231 / 31,658 declarations. Exact **455-module replay**
  (114 GoLean + 134 local + Tests.UnseqHarness + 206 dependencies). All 144
  original files excluding private Lake wiring, including 134 Lean sources,
  match their immutable objects. Ordinary R2 simulation/guarded targets close;
  that frozen input's conditional R1 headers remain unchanged. Both alias
  executions retain exact `{-2,7}` and accept the behavior-set certificate
  (8 leaves, 6 sites, 342 steps; certificate 226 nodes / 231 edges / 6 dedup hits).
- Existing D1/U1 experimental packages: **PASS97 / PASS83**, exhaustive audits
  (22,708 / 20,296 declarations), headline checks, and exact replay of their
  eight / three source modules. Their imported GoLean modules are covered by
  the full upstream replay. No experiment source/target was weakened.

Every replay command exited successfully; the `replaying MODULE` multisets
match built outputs and requested source inventories exactly, without missing,
extra or duplicate modules. The immutable consumer aggregates retain RD5
Set/Keep/Pair/Alias/Add, RD6's original conditional program acceptance with
InitAssembly explicit, RD7's downstream assembly/initialized-program theorems,
and original observation contracts. This does not alter logic's current R1
uptake or ask it to repin.

| Scope | Historical unresolved | Candidate unresolved |
| --- | ---: | ---: |
| Narrow upstream D1/U1 import closure | 16 | **FAIL13** |
| Frozen phase/I2 consumer closure | 21 | **FAIL18** |
| Actual R2 aggregate/alias closure | 47 | **FAIL44** |
| R2 plus full GoLean root | 51 | **FAIL48** |
| Full GoLean root without downstream modules | distinct scope | **FAIL43** |

Exact set comparisons remove only the three affected renderer helpers. The
remaining narrow upstream set is derived Expr/Stmt BEq, Stmt Repr, SeedValue
Repr, and the nine Declaration Ty/Field/Method Repr helpers. The five downstream
findings remain `GoLean.IrisCustomer.pathTags_persistent` and the four
`GoLean.Logic.Source.instRepr{ScalarTy,FieldTys}.repr_{1,2}` implementations.
R2 adds the unchanged 26 CLI/parser/explorer helpers recorded in the immutable
R2 stage; the full root adds the same four ChoiceTrace helpers. All these names
retain their `._unsafe_rec` suffix (and the existing private module prefix
where applicable). None is waived. The exact full upstream count excludes
those five logic findings and is therefore not the 48-finding combined scope.
Generated implementations with safe total kernel parents are counted separately:
229 in the full upstream renderer audit, 274 in phase, 316 in actual R2, 321 in
R2 plus full root. Merely renaming a helper would not pass these comparisons.

No live logic checks were rerun or reclassified: the inherited Memory warning
and historical live **35 NOT-PUBLIC** failure stay visible. This bounded repair
does not complete general locality, concurrent/infinite adequacy, parser/explorer
correspondence, or the full replacement reasoning interface. It introduces no
Iris reasoning or extra consumer correctness premise.

Implementation pin: `ccc54f4f152b3e01603799526d0e3949e74a7a71`.
CI and corpus checks ran **before this commit**: their metadata names the
starting HEAD and marks the worktree **DIRTY**. No commit-clean CI run is claimed.
The three production-file SHA256 values recorded during validation remained
unchanged and were checked against this commit; every one of its 14 changed/new
files matched its committed blob and working bytes at implementation commit
creation. Subsequent handoff edits are documentation and verbatim preservation of the
reviewer’s already-checked source probes; production sources
remain identical to that pin. The three experiment
proof/audit files also match the independently built private package exactly.
Consumer source identity and replay multisets were checked separately as above.
Final review requested this explicit precommit provenance statement; it is a
reporting correction, not a changed source or a reason to reuse mismatched input.

The fresh [independent review](2026-10-15_relational-rendering-review.md) accepts
`ccc54f4f152b3e01603799526d0e3949e74a7a71` for this bounded handoff: no new
semantic defect or preservation blocker. It independently checked affected
elaboration/replay, source identities, module multisets and finding-name sets;
its report distinguishes those checks from inspection of author CI/consumer
runs. The report is saved verbatim. The reviewer’s two already-checked source
probes are also copied byte-for-byte into
`experiments/2026-10-15-rendering/review/` for source preservation; their original
scratch copies remain. No production file or accepted target changes in the
handoff commit. Remaining limits and unwaived failures are exactly those above.


[USER] 2026-10-15: finish only this renderer candidate's validation, independent
review and immutable handoff, then park while the relational architecture is
reassessed. Preserve all source. No new increment, integration, merge or push.
The owned branch/source worktree and private source inputs are retained; only
reconstructible build outputs and logs may be removed after review is saved.


Parked after this handoff. Removed this lane's root `.lake/build`, each private
old/consumer/renderer-check package's `.lake/build` (including its independent
dependency build directories), D1/U1 experiment `.lake/build`, `.tmp/gocache`,
reviewer compiled outputs, validation logs and corpus execution outputs.
Per the final source-preservation instruction, retained the source worktree,
private old/consumer/dependency sources, reviewer source probes, and generated
Go/lowered-input JSON sources. No source archive or peer checkout was deleted.
The committed implementation, report and reproduction instructions are the
handoff; no new increment, integration, repin, merge or push was performed.
