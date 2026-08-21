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

**REWRITTEN 2026-08-18 (delta-review fix round).** The previous text
called this a forced point with no latitude entry, and described the
construction as the spec's algorithm over the complete program's
package list. Both claims were wrong, and the ways they were wrong are
observable from Go source. What follows is the measured rule.

**Within a package** (`spec#Package_initialization`) — unchanged and
genuinely forced: variable initializers in dependency/declaration
order (go/types' `InitOrder`), then `init()` functions in file/source
order.

**Between packages.** `spec#Program_initialization` says: "Given the
list of all packages, sorted by import path, in each step the first
uninitialized package in the list for which all imported packages (if
any) are already initialized is initialized", and
`spec#Program_execution` defines the complete program as main "with
all the packages it imports, transitively". gc's schedule departs from
that text in two ways.

*(1) The node set is PRUNED.*
`cmd/compile/internal/pkginit/init.go`, `MakeTask`, emits a
`..inittask` record for a package only if it has residual
initialization work or an inittask-bearing import:

```go
if len(deps) == 0 && len(fns) == 0 &&
   path != "main" && path != "runtime" { return }
```

`fns` is what survives `cmd/compile/internal/staticinit` (a variable
initializer folded into the data section leaves nothing to run; an
`init` function with an empty body is dropped) and `deps` is the
imports that themselves bear records.
`cmd/link/internal/ld/inittask.go`, `inittaskSym`, then walks exactly
those records. A package with no record is NOT IN THE SCHEDULE: it
gates nothing, and its importers are ready one step earlier than the
spec's text predicts. Pinned by `multipkg/init-order-pruned` (the
static/dynamic pair, with the dynamic subject as the control) and
`multipkg/init-order-pruned-stdlib`.

*(2) The tie-break is by LINKER SYMBOL NAME, not import path.* The
linker pops the lexicographically first ready record by
`ldr.SymName` — `objabi.PathToPrefix(path) + "..inittask"`. Appending
the suffix is not order-preserving: `"x" < "x-y"` as paths, but
`"x-y..inittask" < "x..inittask"` as symbols, because `'-'` (0x2d) <
`'.'` (0x2e). `PathToPrefix` additionally percent-escapes
symbol-hostile bytes and any `'.'` after the last `'/'`, which is live
in the standard library today (Go 1.26 ships
`crypto/internal/entropy/v1.0.0`). Pinned by
`multipkg/init-order-tiebreak`.

**The real construction** (`tools/nativefrontend/inittask.go` for the
rule and its evidence, `load.go`'s `specInitOrder` for the walk):

1. Build the graph over the source units plus the transitive closure
   of their non-source imports, keyed by `PathToPrefix` of the import
   path — the namespace gc's edges and sort key live in. Source edges
   come from the import DECLARATIONS, which is what the compiler's
   `Target.Imports` is.
2. Compute the node set to fixpoint: a package is a node iff it has
   residual work of its own or imports a node.
3. Walk the nodes, taking the lexicographically first READY one by
   `prefix + "..inittask"` at each step.
4. Emit the PRUNED source units first, then the scheduled ones in walk
   order. This is the faithful placement, not a fallback: a pruned
   package's initializers are exactly the ones gc folded into the DATA
   SECTION, so their values are in place before any init code runs
   anywhere, and a pruned package can hold nothing but constants, so
   nothing it assigns can depend on another package's run-time value.

`main` is always a node (gc emits its record unconditionally) and is
always last: every source unit is reachable from `main` by imports,
and a chain ending at a node is all nodes, so no source node can be
scheduled after it.

**Where the node facts come from.** For SOURCE packages, syntactically:
a `func init()` with a non-empty body is work, and a package-scope
variable initializer is work unless go/types folded it to a constant.
For STDLIB packages, nothing the frontend can see decides it — whether
`sync/atomic` has residual init work is a fact about compiled objects —
so the answer is taken FROM THE COMPILER. `scripts/gen-inittask-table`
runs `go list -export` over `std` and reads each archive with
`go tool nm`: a defined `p..inittask` means p is a node, and the
undefined `q..inittask` references ARE p's edges. The result is the
tracked, dated `tools/nativefrontend/inittask-std.tsv` (362 rows at
go1.26.5, 293 of them nodes), embedded into the frontend and
regenerated when the Go pin moves.

That table also RETIRES the old `go/build` reading of stdlib imports
and the caveat that went with it — gc's own `deps` list is now read
directly, so the question of whether export data lists imports the
package does not declare no longer arises.

**The approximation's direction, honestly.** `staticinit` folds
strictly more than "go/types says constant": composite literals of
static elements, copies from other statically initialized globals,
addresses of globals, conversions of constants, and — with the inliner
on — whole function calls. So the syntactic rule UNDER-PRUNES: it can
call a package a node that gc pruned, never the reverse. Over-pruning
would be the unsafe direction (it deletes a real edge); under-pruning
keeps a spurious one, which can delay an importer past a package it
should have beaten. That is a real divergence, and it is MEASURED, not
assumed: a 26-flavor probe puts it at 11 of 26, all one-directional,
recorded in the divergence ledger and pinned by
`multipkg/init-order-staticinit` (BUG-061).

**And this is a LATITUDE point, not a forced one.** One residual
flavor settles it: for `var X = f()` with `f` foldable, `go run`
reports one order and `go run -gcflags=all='-N -l'` reports the other,
for the same source under the same compiler. Package initialization
order is therefore not determined by the spec plus the program at the
pruning boundary — it depends on the optimizer. The corpus cases pin
gc-at-default-flags, which per the doctrine is a deterministic gc-pin
of latitude carrying a re-envelope obligation, not a fidelity
achievement. All five landed init-order cases were checked under
`-gcflags=all='-N -l'` and are stable there; only the call-folding
flavor moves. Ledger entry L-011.

Type-check order is a SEPARATE, weaker requirement (any dependency
order will do) and is computed over the local units only; conflating
the two is what produced BUG-060.

The frontend then synthesizes ONE `$pkginit` whose body is the
concatenation of per-package segments in that package order (each
segment: the package's `InitOrder` assignments, then its `$initN`
calls). gids are assigned in the same order, so driver seeding is
unchanged. Guardrails: `multipkg/init-order` (schedule order beats
import-declaration order; var-before-init within a package),
`multipkg/init-order-stdlib` (the ordering effect of a stdlib package
that IS a node — BUG-060's pin), `multipkg/init-order-pruned{,-stdlib}`
(pruning, with a control), `multipkg/init-order-tiebreak` (the symbol
sort key), `multipkg/init-order-staticinit` (the residual, RED),
`multipkg/diamond-import` (exactly-once initialization, dependencies
first).

Recorded honestly: which packages are in the schedule is
BUILD-CONDITIONED, because build constraints decide which imports a
stdlib package declares on a given GOOS/GOARCH — and now also
TOOLCHAIN-conditioned, because the table is read from one toolchain's
compiled archives. Both are properties of Go rather than modeling
choices, and the frontend reads the same host configuration the
`go run` oracle uses, so the two legs agree by construction. A port to
another platform or a move of the Go pin re-derives the table;
`scripts/gen-inittask-table` is the one command that does it.

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
- **A non-source import the inittask table does not cover**: refusal
  (`stdInitLookup`, `tools/nativefrontend/inittask.go`). This is the
  audit-F1-D class, restated for the table route and NOT narrowed by
  it. Whether a package is a node of the initialization schedule is a
  fact about compiled objects; if the frontend cannot read that fact
  it cannot place the package, and treating it as a leaf silently
  perturbs the order of every package around it. So the export
  refuses. **The honest loss:** an import that go/types CAN resolve but
  the table cannot name is now unlowerable — a vendored dependency, a
  GOPATH package outside `std`, a std package added after the table was
  generated, and the six `std` directories with no buildable non-test
  Go files (recorded in the table as `?`, refused explicitly rather
  than defaulted). Before the table this class refused too, via
  `go/build` failing to resolve the path; the boundary moved, the
  fail-closed posture did not. Regenerating the table
  (`scripts/gen-inittask-table`) is the fix when the cause is a moved
  Go pin; a genuinely non-std dependency is outside what the frontend
  models and belongs in §4's normalization discussion, not here.
- **Dot imports (`import . "p"`)**: a dot import of a SOURCE package
  refuses at the loader — new capability, closed by default. The
  recorded pre-existing stdlib dot-import defect (stdlibshim.go
  FAIL-CLOSED RULES: dangling plain call → runtime `stuck`, recorded
  2026-08-16) is deliberately NOT fixed or widened here.
- **Stdlib shims** (`E5`) are injected PER UNIT. (Superseded text: this
  section originally said shims "stay MAIN-PACKAGE-ONLY" — raft W4.0
  widened injection to every source unit, `load.go` `newSourcePkg`'s
  `injectStdlibShims` call before that unit's type-check, because
  raft's `errors.New` sentinels live in non-main units. Corrected
  2026-08-21, holes arc — the census's G-35 row and its §10 drift note
  flagged the stale claim.) Reserved-name collisions in ANY unit
  refuse loudly; a call to a non-allowlisted stdlib function keeps the
  standing selector refusal, in every unit alike.
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
