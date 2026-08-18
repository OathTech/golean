# Multi-package identity design (raft W1.1, 2026-08-18)

Status: DESIGN OF RECORD for the multi-package lowering arc (master
plan `docs/2026-08-15_raft-master-plan.md` §W1.1 — the critical path's
head; scoping `docs/2026-08-15_raft-push-p0-scoping.md` §7 Blocker 1).
Written BEFORE implementation, per the guardrails-first contract; the
guardrail family is `Corpus/coverage/exec/multipkg/*` (8 rows landed
red in the guardrails slice; 9 after `cross-var` joined in the
implementation slice, 11 case ids after the audit-fix round's
`init-order-stdlib` — §8). The prerequisite defect is BUG-010 (`docs/BUGS.md`): TypeId keys
qualified by package NAME where Go keys identity on the import PATH.

## §1 The identity rule

**Go's semantic type identity is keyed on the import path** (spec
§Type identity: a defined type is different from any other type; two
same-named exported types from packages at different import paths are
distinct — gc's own panic text names the class, "types from different
packages"). Function identity likewise: a package-level `F` is the
declaration at its package, and packages are identified by path.

### TypeId key grammar (the BUG-010 fix)

    TypeId.key := <qualifier> "." <TypeName> [ "[" targs "]" ]
    qualifier  := the declaring package's IMPORT PATH
                  ("main" for the package under lowering)

- `qualifiedTypeName` (tools/nativefrontend/emit.go) switches its
  qualifier from `pkg.Name()` to `pkg.Path()`. This is the ONE
  boundary constructor for TypeId keys (mangled instantiation keys
  compose it via `renderTypeArg`/`instTypeId`, so type arguments
  inside brackets re-key consistently for free).
- **Existing corpus keys are unchanged**: the main package's path is
  its name (`conf.Check("main", ...)`), and every stdlib package the
  green corpus lowers types from is single-segment (`strings`, `fmt`,
  `sync`, `slices`) — path == name, byte-identical keys. The one
  baseline row this re-keying moves is the BUG-010 pin itself
  (`interfaces/imported-package-name-collision`, frontend-export →
  expected PASS), plus the new multipkg flips.
- `checkPackageNameCollisions` (the v1 fail-closure) RETIRES: with
  path qualifiers, two distinct declaring packages can no longer mint
  one key, so the check it performed is vacuous. Its registry
  (`qualPkgPaths`) is replaced by the §3 grammar guard at the same
  boundary.

### Key-grammar injectivity argument

Go identifiers contain neither `.` nor `/` (spec §Identifiers), and
the §3 guard refuses DOTTED import paths. Therefore in every admitted
key the FIRST `.` of the bracket-free head separates qualifier from
type name, and distinct (path, name) pairs give distinct keys. FuncId
keys (below) inherit the same argument: a bare main-package function
name contains no `.`; a qualified one has exactly one `.` before the
name; a method key `<TypeId>.<method>` has exactly two (its TypeId
head is dot-free path + one separator); synthetic ids use `$`, which
identifiers cannot contain. No two constructors can emit one string.

### FuncId key grammar

    plain func, main package:   <Name>            (unchanged — the
                                                   subject namespace)
    plain func, other package:  <import-path> "." <Name>
    method:                     <recv TypeId> "." <Name>  (unchanged
                                                   rule; re-keys with
                                                   its TypeId)
    init functions:             "$init" N   (main)
                                <import-path> ".$init" N  (others)
    lifted literals:            <enclosing FuncId> "$lit" N
    generic stencils:           <FuncId> "[" targs "]"

Main-package functions stay BARE deliberately: they are the corpus
subject namespace (`--function` lookup, `main.F` observations, every
pinned lowering), and dot-free bare names cannot collide with
qualified keys (grammar argument above). The minting goes through one
new boundary helper (`funcWireName`), used by the declaration loop,
the static-call arm, the func-value arm, and the new qualified-call
arm. Stdlib (non-source) function objects do NOT qualify — see §6
dot-import note.

### Package-level variables (globals)

The wire global NAME qualifies the same way (`<path>.<name>` for
non-main); gids stay a dense PROGRAM-wide index, assigned per package
in the §5 initialization order (the single gid source rule is
unchanged — `collectGlobals` runs once per package, in that order).
The decoder's duplicate-global refusal is the standing boundary
collision check.

## §2 Where qualification lives

Frontend-only. GoCore continues to see opaque `TypeId`/`FuncId`
strings; `Ty.eqb`'s `.defined a == .defined b` arm is UNCHANGED and
now decides Go's real identity because the frontend mints real
identities. NativeToIR is unchanged structurally — its standing
decode-boundary collision checks (duplicate FuncId, duplicate TypeId,
duplicate global, globaladdr bound) are the checks this design relies
on downstream. No new wire keys are introduced by the identity change
itself.

## §3 The rendering residue (argued, not hidden)

GoCore renders `TypeId.key` in two observation-bearing channels:

- `TypeId.unqualified` (GoLean/GoCore/Value.lean) — the
  reflect-`Name()` observation contract — strips the head before the
  FIRST `.`;
- `goTypeNameForMessage` / `dynamicTypeName?` (GoLean/GoCore/Ops.lean)
  — panic-message fidelity — renders the key VERBATIM.

gc renders panic qualifiers with the package NAME (`template.T`,
`inner.T`), and where two names collide gc's own text is AMBIGUOUS
plus the suffix `(types from different packages)`. Consequences, per
path shape:

1. **path == name** (single-segment, package named after its dir —
   `main`, all corpus subpackages by construction, all of vendored
   raft per §4, single-segment stdlib): BOTH channels render exactly
   what gc renders. No residue.
2. **dotted path** (`go.etcd.io/...`, `gopkg.in/...`): would break
   `unqualified`'s strip — the observation typeName itself goes
   wrong. REFUSED at the boundary (the grammar guard that replaces
   `checkPackageNameCollisions`): "dotted import path ... — vendor at
   a dot-free path". Nothing in scope needs them (§4).
3. **multi-segment dot-free path** (`html/template`, `red/inner`):
   identity decisions are now CORRECT (the BUG-010 fix), and
   `unqualified` still strips correctly (the first `.` is still the
   separator), but a PANIC MESSAGE naming such a type renders
   `red/inner.T` where gc prints `inner.T`. This divergence is
   differential-visible (an observation mismatch, a red case — never
   a silent wrong identity answer) and is pinned deliberately red by
   `multipkg/same-name-identity-panic`. It is NOT fixable
   frontend-side: no single key string can simultaneously be
   path-injective and byte-equal to gc's deliberately ambiguous
   name-qualified message. The structural fix is separating display
   from identity in GoCore (a display-name table or field) — a
   semantic-core change, OUT OF THIS ARC'S SCOPE by charter, filed as
   BUG-059 with the pinned witness. It does not gate raft (§4 keeps
   raft in shape 1).

## §4 Vendored-vs-module path normalization (the raft ruling)

**Canonical vendored form: short, dot-free, single-segment import
paths equal to the package name** — `raft`, `tracker`, `quorum`,
`confchange`, `raftpb` — i.e. the module prefix `go.etcd.io/raft/v3/`
is stripped by a mechanical, uniform import-rewrite when the subject
is vendored into the corpus tree. Rationale:

- shape-1 rendering (path == name): panic/observation fidelity is
  exact BY CONSTRUCTION, because the go-run oracle compiles the SAME
  vendored tree with the same short paths — both bounds see one
  program.
- dotted module paths are unrepresentable in the key grammar (§3.2),
  and normalizing to short paths is the smallest recorded delta.
- the rewrite is a RECORDED subject delta (the W2 delta ledger;
  covmap — `docs/2026-08-17_covmap-pilot.md` — is the candidate
  tracking mechanism per the operator cross-read). A future
  module-mode frontend that admits full module paths must revisit §3
  first; that obligation is recorded in BUG-059's entry.

## §5 Cross-package initialization (the E7 semantics)

Forced point, no latitude entry: since Go 1.21 the spec pins the whole
schedule. Two clauses, and the arc's first implementation conflated
them (audit F1 / BUG-060) — so state them separately.

**Between packages** (`spec#Program_initialization`): "Given the list
of all packages, sorted by import path, in each step the first
uninitialized package in the list for which all imported packages (if
any) are already initialized is initialized." The list is the COMPLETE
PROGRAM's: `spec#Program_execution` defines that as the main package
"with all the packages it imports, transitively". **The imported
stdlib packages are in that list**, and their presence is observable
even though nothing about their bodies is — they stand between a
source package and its readiness, so a source package that imports one
cannot be scheduled until it has run.

**Within a package** (`spec#Package_initialization`): variable
initializers in dependency/declaration order (go/types' `InitOrder`),
then `init()` functions in file/source order.

**The real construction** (`tools/nativefrontend/load.go`,
`specInitOrder`): build the node set as the source units plus the
transitive closure of every non-source import, take each node's
dependency edges from its import DECLARATIONS (source units from the
AST; non-source packages from `go/build`, which reports the actual
import clauses build-constraint-filtered for the host — deliberately
not `types.Package.Imports()`, whose export-data list is neither a
subset nor a superset of the import clauses: at Go 1.26 `sync`'s lists
`internal/abi`, which it does not import, and omits `runtime`, which
it does), then run the spec's lexicographic-first-ready walk over the
whole set. Non-source packages occupy their positions and are then
dropped from the result: they contribute NO emitted initializer —
their bodies are not modeled — and only their ORDERING EFFECT lands,
which is computable from the import graph alone without modeling
anything. Fail closed: an import path `go/build` cannot resolve refuses
the export rather than being treated as a leaf, because a missing edge
silently perturbs the schedule. A single source unit short-circuits
(one package, one position), so single-package cases keep exactly the
old path and cost.

Type-check order is a SEPARATE, weaker requirement (any dependency
order will do) and is computed over the local units only; conflating
the two is what produced BUG-060.

The frontend then synthesizes ONE `$pkginit` whose body is the
concatenation of per-package segments in that package order (each
segment: the package's `InitOrder` assignments, then its `$initN`
calls). gids are assigned in the same order, so driver seeding is
unchanged. Guardrails: `multipkg/init-order` (path-sorted order beats
import-declaration order; var-before-init within a package),
`multipkg/init-order-stdlib` (the stdlib nodes' ordering effect —
BUG-060's pin), `multipkg/diamond-import` (exactly-once
initialization, dependencies first).

Recorded honestly: which packages are in the list is
BUILD-CONDITIONED, because build constraints decide which imports a
stdlib package declares on a given GOOS/GOARCH. That is a property of
Go, not a modeling choice, and the frontend reads the same host
configuration the `go run` oracle uses, so the two legs agree by
construction. A port to another platform re-derives the list.

## §6 Fail-closed register (what refuses, what is unchanged)

- **Import resolution rule**: an import path resolves to (a) the case
  directory subtree — a subdir at exactly the import path containing
  non-test .go files — else (b) the stdlib importer. IMPORT-DRIVEN
  discovery only: subdirectories never named by a (transitive) import
  are inert (nested corpus case dirs stay cases, not packages).
  Anything resolving to neither: refusal (today's `type-check: could
  not import` becomes an explicit path-shaped refusal). A path that
  resolves to BOTH stdlib and a subdir: refusal (shadowing ambiguity,
  never a precedence guess).
- **Dotted import paths**: refusal (§3.2).
- **Import cycles**: refusal (go/types cannot admit them; the loader
  refuses with the cycle named rather than recursing forever).
- **Dot imports (`import . "p"`)**: a dot import of a SOURCE package
  refuses at the loader — new capability, closed by default. The
  recorded pre-existing stdlib dot-import defect (stdlibshim.go
  FAIL-CLOSED RULES: dangling plain call → runtime `stuck`, recorded
  2026-08-16) is deliberately NOT fixed or widened here.
- **Stdlib shims** (`E5`) stay MAIN-PACKAGE-ONLY: a source package
  calling `strings.Fields` keeps the standing selector refusal. The
  W1.2 `slices.SortFunc` work inherits this seam decision and may
  widen injection to source packages with its own fidelity argument.
- **cgo (`import "C"`), embed, unsafe, reflect**: unchanged standing
  refusals (none become admissible via the new loader; `C` is not a
  subdir and not stdlib → path refusal; runtime-touching stdlib keeps
  its per-decl quarantines).
- **`internal/` visibility** is a go-tool rule, not a go/types rule:
  the corpus convention simply avoids `internal` paths; none of the
  raft target's five packages uses one. Recorded as a non-check.
- **BUG-018's function-local-type parameterization,** the sync-type
  special case (`Pkg().Path() == "sync"`), and the D5 imported-marker
  machinery are unchanged except that D5's "imported" test becomes
  "not a SOURCE package" (source-package types now get real TypeDefs
  from their own package's declaration pass).

## §7 The corpus + oracle convention

A multi-package case is a case dir whose main package imports
case-relative subdir paths (`import "mathutil"`, `import
"red/inner"`). Both pipeline legs resolve them identically:

- **Frontend**: `--dir` loads the main package, then import-driven
  source-package discovery per §6, type-checked in dependency order
  with a chained importer (source map first, `importer.Default()`
  fallback).
- **go-run oracle**: `tools/coverageharness` copies each
  transitively-imported subdir into `<out>/gopath/src/<path>` beside
  the assembled main package, and `scripts/diff-coverage` runs the
  oracle with `GOPATH=<out>/gopath` (absolute) under the existing
  `GO111MODULE=off` — Go's own GOPATH resolution is the oracle-side
  authority, so a resolution disagreement is a visible red, never a
  harness invention.

## §8 Blast-radius prediction (checked at re-pin time)

- Existing single-package cases: ZERO key changes (§1), so zero
  drift expected outside:
  - `interfaces/imported-package-name-collision`: frontend-export →
    PASS (the BUG-010 closure flip; the case's doc comment updates
    with it);
  - the 9 new `multipkg/*` rows: 8 → PASS;
    `multipkg/same-name-identity-panic` stays FAIL (observation
    stage, the §3.3 residue, BUG-059's pin).
    (Written as 8 rows before implementation; corrected to 9 after the
    fact — `multipkg/cross-var` was added DURING the implementation
    slice, as a same-slice guardrail for the qualified
    store/compound-assign/&-alias paths that the slice's fail-closed
    junk message exposed. The prediction's shape held; the count did
    not, because the guardrail set legitimately grew.)
- Any OTHER drift at the full-run re-pin is a finding to investigate,
  not to launder (CLAUDE.md baseline rules).
- Recorded after the pre-merge audit: the prediction above is a
  prediction about DRIFT, and it held — but a green re-pin says
  nothing about behavior no case exercises. Audit finding F1 (BUG-060)
  was exactly that: the initialization list omitted the stdlib nodes,
  and no corpus case had a local package gated by a stdlib import, so
  every gate stayed green. `multipkg/init-order-stdlib` closes that
  hole (2 rows, red-then-green across the audit-fix round).
