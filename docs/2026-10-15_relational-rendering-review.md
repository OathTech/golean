# Independent executed-renderer review

Verdict: accept the bounded renderer correspondence candidate
`ccc54f4f152b3e01603799526d0e3949e74a7a71` for immutable handoff. No remaining
new semantic defect or preservation blocker was found. This is not approval
to merge, push, integrate, repin logic, or complete the full reasoning interface.

Scope: the charter `2026-10-15_relational-renderer-correspondence-charter.md`,
baseline `82353580814b66399cdc472a4c4edf9044d0c097`, and the renderer follow-up
in `relational-rendering-1015`, including the final stage/reproduction records
and frozen acceptance evidence. No earlier review verdict is an assumption.

Source inspection:

- `Rendering.app` retains the derived algorithm's left-associated append,
  constructor spelling, line insertion, nesting based on `prec >= max_prec`,
  grouping and outer `Repr.addAppParen`, including nullary constructors.
- Recursive direct arguments use `max_prec`; list/array element rendering
  uses precedence zero. `Option.some` renders its recursive argument at
  `max_prec`. These agree with the pinned deriving-Repr, List, Array and
  Option definitions in Lean 4.32.2.
- List rendering uses `bracket`, whereas arrays use `bracketFill`. These
  distinctions are observable at narrow widths and are retained.
- Pair rendering uses the original key/value order, corresponding to
  `Prod.reprTuple`'s accumulated list followed by reversal. Neither replaced
  recursive second component has a special `ReprTuple` instance.
- Nested `Loc` rendering is direct-recursive and its old derived renderer
  is transparent; SliceValue, MapValue, ChanValue, GoString and SyncPrim
  renderers are also transparent derived definitions. Their presence alone
  does not require replacing them.

Findings and dispositions:

- The initial `Closure.lean` imported only StepFn and failed at the missing
  stepMulti root after the stepFn report. This is incomplete evidence, not an
  all-driver pass. Fixed: the retained probe imports Multi and all three roots
  run successfully against both old and new environments.
- The closure probe initially selected declarations by name root, which can
  omit private declarations. The author changed it to defining-module
  ownership. An independent module-owned traversal produces the same counts:
  2,264 / 2,507 / 2,355 project nodes for stepFn / stepMulti / runProgramM,
  with no opaque project endpoints. No actual omitted dependency was found.
- Initial representative semantic links did not directly demonstrate a Ty
  diagnostic. Fixed by `dynamic_type_refusal`, with arbitrary Ty and the
  actual `mentionsUnsupported` guard. The reviewer's suggested sync valueEq
  instance was mistaken: that constructor has an explicit unsupported arm.
  No false equation or new reachability claim was retained.
- The source argument initially needed explicit dependency order because the
  GoValue/Expr step equations use the candidate Ty instance. Fixed: the final
  record establishes Ty first and then supplies that result to the other two
  source/derivation inductions. The three equations are not presented as three
  independent equalities to old opaque constants.
- CI/corpus metadata identify a precommit DIRTY worktree. The final handoff
  correction explicitly retains that provenance and binds unchanged production
  hashes to the implementation commit. It must distinguish the fourteen files
  matched at implementation commit creation from later documentation-only
  corrections; no commit-clean CI execution is claimed.

Independent completed checks:

- Compared all three complete constructor-step bodies in Derivation.lean to
  the old deriving traces, not just selected branches. They agree after only
  removing binder decorations/whitespace and replacing recursive function
  names with the recursion parameter.
- Re-elaborated Rendering, Value, Syntax, Derivation and SemanticLinks into
  reviewer-owned outputs with read-only links to built imports. Exact kernel
  replay accepted precisely those five modules. This does not claim a full
  independent dependency rebuild.
- Exhaustively checked 11,672 declarations in the imported StepFn plus
  Derivation/SemanticLinks scope: standard axioms only. All thirteen renderer
  instance, constructor and semantic-site headline theorems use only propext.
  Replayed the independent audit module too. The separate implementation scan
  is FAIL, twelve inherited findings, in this narrower import scope; no waiver
  is inferred from mathematical checks.
- Compared current old/new control outputs byte-for-byte: all 9,821 lines
  agree. These are inspected author executions, not independently rerun
  controls. The source control includes all constructors, precedence on both
  sides of max_prec, narrow widths, indentation/column parameters, nested
  arrays/lists/pairs/options, malformed values and reachable diagnostic sites.
- `git diff --check` passed at source review time.

Preservation assessment:

The constructor bodies are the actual pinned deriving algorithm, and the new
definitions satisfy those bodies as kernel-checked Format-tree equations.
Recursive calls descend through proper finite subvalues, including nested
list/array elements and Option contents. Source-level induction therefore
supports preservation of the old executed algorithm under the existing
pinned compiler/toolchain assumption. This argument establishes Ty first;
GoValue and Expr additionally use that result for their Ty-valued fields.
It retains full Format trees, so preservation extends to all width/indent/
column rendering parameters, not merely the sampled strings. The unchanged
transparent leaf printers and toolchain Format/escaping operations remain
shared dependencies. This is the charter's separately reviewable
source/derivation argument, not a kernel equality to old opaque constants.

Reviewer harness correction: the first independent compile failed because
Lean chose the partially populated private GoLean search root and could not
find Platform. Read-only links to the remaining built imports corrected the
setup; all subsequent elaboration/replay runs succeeded.

Final immutable-input and result inspection:

- Independently checked all three production-file SHA256 bindings against the
  validated files and the immutable implementation blobs. They match exactly.
  Runtime changes are confined to Rendering, Value and Syntax; no operational
  guard, choice/fuel rule, event, error class or continuation is edited.
- Independently extracted immutable logic package sources and compared every
  original file except private Lake wiring: phase input `3c9be98f` matches all
  137 files, including 128 Lean sources; older I2 input `5e8ed98a` matches all
  123 files, including 115 Lean sources; R2 input `6da4e8aa` matches all 144
  files, including 134 Lean sources. Original proof headers therefore remain
  unchanged. Every private dependency clone is clean at its exact pins.json
  revision and has no object alternates.
- Inspected author full CI/differential evidence: PASS, 1,335 seconds,
  263 build jobs, 114 upstream module replays, 396 evaluator checks,
  4,025 differential rows with no regression and 415 negative rows. All
  reported speedbumps pass. This is inspected author evidence, not another
  independent full CI/differential execution.
- Inspected frozen phase/I2/R2 package builds and headline/aggregate audits.
  Independently compared complete replay-name multisets against actual built
  output inventories: phase 451, I2 443, R2 455, renderer experiment 117,
  with no missing, extra or duplicate names. R2's explicitly imported
  Tests.UnseqHarness is included. Fresh renderer replay also succeeds.
  The author reports successful process exits; the observed logs and complete
  multisets agree. These whole-package replays are inspected author evidence;
  the separate limited replays above were run independently.
- Inspected both alias executions: each reports exact projected {-2,7},
  eight leaves, six sites, 342 steps and the accepted 226-node/231-edge
  certificate with six dedup hits. These are executed controls, not a general
  native-driver correctness theorem. The renderer step control projects
  stores/tapes/labels/errors and does not serialize full Config values.
- Independently compared exact implementation-finding name sets, using the
  retained I2 inventory and immutable R2 source groups. Exactly the three
  repaired renderer helpers disappear: narrow upstream FAIL13, frozen
  phase/I2 FAIL18, actual R2 FAIL44, R2 plus full root FAIL48. Full upstream
  without downstream modules is FAIL43. No smaller imported scope or renamed
  unresolved helper is being substituted for a repair. Remaining findings are
  unwaived. The reviewer's narrower StepFn scope FAIL12 is separate again.

Additional reviewer harness corrections: the first replay-inventory comparison
omitted R2's explicitly imported Tests.UnseqHarness and was corrected; the first
expanded finding-name reconstruction used the defining filename StrictJsonParse
as its namespace, corrected to the actual StrictJson namespace. These were
reviewer bookkeeping failures, not candidate failures. Corrected comparisons
passed with exact sets and multisets.

Reproduction of independent checks:

Follow the committed experiment README for the two immutable execution
environments and the three frozen consumers. Run the retained
check-derivation.py against deriving traces from the old pin; compare the full
constructor bodies, not generated candidate expectations. For private reviewer
elaboration, obtain the candidate LEAN_PATH and lean executable with `lake env`,
prepend a reviewer-owned output root, and populate other GoLean imports there
with read-only links to the finished candidate build. Re-elaborate Rendering,
Value, Syntax, Derivation and SemanticLinks with `lean -R <source-root> -o
<review-output>/<module-path>.olean <source>`, using capped and
LEAN_NUM_THREADS=2. Replay exactly those five names with `leanchecker --verbose`.
The independent ReviewAudit uses the retained RendererAudit algorithm but
imports Derivation/SemanticLinks rather than the full GoLean root; compile and
replay it separately. ModuleClosure uses defining-module ownership and the
retained compiler-selected-body walk. Reviewer source probes are preserved at
`.tmp/renderer-review/ReviewAudit.lean` and `ModuleClosure.lean`; no source is
deleted as part of this review.

For immutable-source identity, extract each pinned package with `git archive`,
exclude only lakefile.toml/lake-manifest.json from byte comparisons, and compare
every other archived file with its private copy. Check each private dependency
HEAD/status against pins.json. For replay inventory, enumerate .olean module
names from the candidate GoLean root, each private local output and all three
dependency outputs, adding Tests.UnseqHarness for R2; compare the complete
Counter against `replaying NAME` lines and require successful process exits.
For finding sets, subtract only the three explicit renderer helper names from
the historical inventories, including R2's exact private namespace prefixes,
and compare against every reported TRUST FINDING name.

The source/derivation argument and checked new definitions close this bounded
assignment under the existing Lean compiler/runtime trust boundary. No kernel
theorem equating a new renderer to an old opaque constant is claimed. General
parser/explorer correspondence, locality, concurrent/infinite adequacy and full
interface replacement remain outside this result. The inherited Memory warning
and historical live 35 NOT-PUBLIC failure remain visible and are not freshly
rerun or waived. The candidate should now be handed off immutably and parked
under the user's latest direction; this review authorizes no further increment.
