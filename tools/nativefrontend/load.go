package main

// load.go — multi-package loading and import resolution (raft W1.1,
// docs/2026-08-18_multipackage-identity.md §6/§7). A case directory's
// main package may import SOURCE packages living in subdirectories of
// the same case dir: an import path P is local exactly when <dir>/P
// contains non-test .go files (import-DRIVEN discovery — subdirs never
// named by a transitive import stay inert, so nested corpus case dirs
// are not mistaken for packages). Everything else resolves through the
// stdlib importer, exactly as before. Fail-closed register (§6):
// dotted local paths, `main` as a local path, dot imports of local
// packages, stdlib-shadowing local dirs, and import cycles all refuse
// the export loudly.
//
// CMD/GO'S IMPORT RULES (BUG-219; lane frontend/fix-admission-1027,
// 2026-10-27). The predicate above admitted ANY subdirectory holding
// non-test .go files and mirrored none of the rules the go command applies
// on top of resolution (cmd/go/internal/load/pkg.go loadImport, and in
// module mode the module graph, cmd/go/internal/modload/import.go), so a
// program gc refuses to build was exported and answered. judgeLocalImport
// and judgeLocalUnit below mirror them, each measured at go1.26.5 under the
// runners' environments (the positive harness's GOPATH layout — the main
// package outside GOPATH/src, each imported subdirectory at
// GOPATH/src/<path>; the negative runner's module leg — a go.mod in the
// lowered directory, GOPROXY=off) and refused with gc's own reason as the
// `type-check` rejection class (gc reports each at the import's position,
// after the file set is fixed and before compiling; the class has no
// loader member, and BUG-125's link-time rule and gclimits.go's
// compile-time rules already carry it for gc's non-go/types rejections):
//
//   GOPATH mode (no go.mod governs the lowered directory):
//   (a) a path whose directory exists under GOROOT/src is resolved by gc
//       to GOROOT first, GOPATH never: with no Go files there, «imports
//       vendor: no Go files in GOROOT/src/vendor» (`vendor`, `internal`);
//       with Go files, the standing shadowing refusal;
//   (V) a non-terminating `vendor` element (FindVendor: `vendor/lib`,
//       `lib/vendor/x`; `x/vendor` is its own package): «use of vendored
//       package not allowed» — the main package is outside every vendor
//       tree (disallowVendorVisibility);
//   (I) an `internal` element (findInternal: `internal/x`, `lib/internal/x`,
//       `lib/internal`): the importer must be inside the tree rooted at the
//       parent of `internal` — the main package never is; a case-local
//       importer Q is iff Q has the path prefix (`lib` may import
//       `lib/internal/x`, `a` may not import `b/internal/x`): «use of
//       internal package lib/internal/x not allowed»;
//   (P) a directory whose package clause is `main`: «import "prog" is a
//       program, not an importable package», whoever imports it.
//
//   Module mode (a go.mod governs the lowered directory):
//   (V) as above, gc's module-mode text «vendor/lib must be imported as
//       lib» (the text rule runs before resolution);
//   (M) a case-local path resolves ONLY through the main module's graph —
//       `require P v…` plus `replace P [v] => <dir>` whose directory is the
//       case-local one, with its own go.mod (the BUG-134 row's shape, the
//       control m00) — otherwise gc's reason: a dotless path is «package
//       lib is not in std (GOROOT/src/lib)», a replace without the require
//       «module lib provides package lib and is replaced but not required»,
//       a require without the replace «missing go.sum entry for module
//       providing package lib» (GOPROXY=off), a replacement directory with
//       no go.mod «module ./lib: reading lib/go.mod: no such file»; a
//       replace pointing at ANOTHER directory is refused by name (gc builds
//       the other directory — measured: a different answer — and this
//       lowering reads case-local directories only); a `vendor` directory
//       at the module root beside such an import is refused by name — gc
//       is in vendor mode there (go 1.14+) and reads vendor/modules.txt and
//       the vendor tree, not the replacement («inconsistent vendoring»
//       without the file, measured);
//   (I) by import path (the importer's module path: the main package's is
//       the module path plus its directory, a replaced module's its require
//       path; a top-level `internal/x` has the empty parent, which every
//       importer is inside — gc accepts the replace-backed `internal/x`,
//       measured; `lib/internal/x` from `test` is refused);
//   (P) as above.
//
//   Legal neighbours, unchanged: `_lib`, `lib/_x`, `testdata/lib` (gc skips
//   such directories only when matching patterns), `lib/vendor` and
//   `x/internal`'s own importer, the require+replace control, and a
//   `main` function of an imported package (an ordinary function).
//
// PROGRAM INITIALIZATION ORDER (design note §5; audit F1, delta-review
// F1). The schedule is gc's, not the spec's literal reading, and the
// rule plus its evidence live in inittask.go — read that first.
// specInitOrder below is the walk: build the graph over the source
// units plus the transitive closure of their non-source imports,
// compute gc's PRUNED node set (a package is a node iff it has
// residual init work or an inittask-bearing import), and take the
// lexicographically first READY node at each step BY LINKER SYMBOL
// NAME. Non-source nodes occupy their positions and are dropped from
// the result: their bodies are not modeled, only their ORDERING
// EFFECT lands. Both departures from the spec's text are pinned:
// multipkg/init-order-pruned{,-stdlib} for the pruning,
// multipkg/init-order-tiebreak for the symbol-name sort, and
// multipkg/init-order-stdlib for the ordering effect that survives
// pruning (BUG-060).

import (
	"fmt"
	"go/ast"
	"go/importer"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"slices"
	"sort"
	"strconv"
	"strings"
)

// sourcePkg is one source package of the program under lowering: the
// main package (path "main", always LAST in program initialization
// order) or a case-local imported package (path = its case-relative
// import path). The emitter switches its per-package state (e.pkg,
// e.info) to a unit while emitting that unit's declarations.
type sourcePkg struct {
	path  string
	files []*ast.File
	info  *types.Info
	pkg   *types.Package
	// $init function wire names of THIS package, source order —
	// consumed by the program-wide $pkginit synthesis.
	initNames []string
	// Import paths of the LOCAL packages this package imports — the
	// TYPE-CHECK dependency edges. NOT the initialization-order edges:
	// those range over the whole program (specInitOrder).
	localImports []string

	// LIBRARY units (stdlib source-through, stdlibsource.go): a standard
	// library package loaded from the pinned GOROOT source. library
	// flags the unit; libFiles are the selected source files (the pin
	// manifest's rows); linknamed maps a `//go:linkname`d local name to
	// its directive (body-less pulls quarantine/poison by name); reached
	// is the reachability-pruned declaration set (stdlibreach.go) — nil
	// for non-library units, which are emitted whole.
	library   bool
	libFiles  []string
	linknamed map[string]string
	reached   *reachSet
	// overlaid: the overlay sites (stdlib-overlay.tsv, "<pkg>/<file>:<line>")
	// applied to this unit's text, in table order — the record of what
	// hand-written text the lowered unit carries (slice 2).
	overlaid []string
	// initKinds: the BUG-061 classifier's kind of every InitOrder entry's
	// initializer, keyed by the entry's Rhs (staticinit.go initKindsOf;
	// filled by loadProgram once the program is type-checked). Read by
	// the E7 detector (hiddendep.go): a hidden read of a variable whose
	// initializer is certain WORK cannot be reordered by gc's folding.
	initKinds map[ast.Expr]initializerKind
}

// newTypesInfo builds the per-package types.Info with every map the
// emitter reads (the same set main.go historically built for the one
// package; see the field comments there).
func newTypesInfo() *types.Info {
	return &types.Info{
		Types:      map[ast.Expr]types.TypeAndValue{},
		Defs:       map[*ast.Ident]types.Object{},
		Uses:       map[*ast.Ident]types.Object{},
		Selections: map[*ast.SelectorExpr]*types.Selection{},
		Implicits:  map[ast.Node]types.Object{},
		Instances:  map[*ast.Ident]types.Instance{},
	}
}

// loader discovers, parses, and type-checks the case's local packages.
type loader struct {
	fset    *token.FileSet
	rootDir string
	// discovered local packages by import path (un-type-checked until
	// checkAll).
	locals map[string]*sourcePkg
	// stdlib importer + probe cache (nil entry = not importable).
	stdlib      types.Importer
	stdlibProbe map[string]bool
	// The library pin (baselines/stdlib-pin.tsv), loaded on the FIRST
	// allowed-library import and reused; nil until then. The rev check
	// of the source root runs at the same moment (stdlibsource.go).
	libPin map[string]string
	// The main unit, registered by loadProgram so the BUG-061 classifier
	// (staticinit.go) can index every source body of the program.
	mainUnit *sourcePkg
	// Declaration index for the classifier's callee-body test, built on
	// first use after type-checking (staticinit.go funcDeclOf).
	funcDecls map[*types.Func]*ast.FuncDecl
	declInfo  map[*ast.FuncDecl]*types.Info
	// The go.mod governing rootDir (modfile.go moduleFor), nil in GOPATH
	// mode; mainName is the main unit's path (its package name), the
	// importer identity the import rules test (BUG-219).
	mod      *modFile
	mainName string
}

func newLoader(fset *token.FileSet, rootDir string) *loader {
	return &loader{
		fset:        fset,
		rootDir:     rootDir,
		locals:      map[string]*sourcePkg{},
		stdlib:      importer.Default(),
		stdlibProbe: map[string]bool{},
	}
}

// isStdlib probes the default importer once per path.
func (l *loader) isStdlib(path string) bool {
	if ok, seen := l.stdlibProbe[path]; seen {
		return ok
	}
	_, err := l.stdlib.Import(path)
	l.stdlibProbe[path] = err == nil
	return err == nil
}

// localDirFor reports whether the import path names a case-local
// package directory (a subdir at exactly the path, holding non-test
// .go files). Paths that could escape the case dir are never local.
func (l *loader) localDirFor(path string) (string, bool) {
	if path == "" || strings.HasPrefix(path, "/") || strings.Contains(path, "..") {
		return "", false
	}
	clean := filepath.ToSlash(filepath.Clean(filepath.FromSlash(path)))
	if clean != path {
		return "", false
	}
	dir := filepath.Join(l.rootDir, filepath.FromSlash(path))
	fi, err := os.Stat(dir)
	if err != nil || !fi.IsDir() {
		return "", false
	}
	entries, err := filepath.Glob(filepath.Join(dir, "*.go"))
	if err != nil {
		return "", false
	}
	for _, f := range entries {
		if !strings.HasSuffix(filepath.Base(f), "_test.go") {
			return dir, true
		}
	}
	return "", false
}

// discover walks the given files' imports, parsing every reachable
// local package (transitively). importerPath names the importing
// package for refusal messages.
func (l *loader) discover(importerPath string, files []*ast.File) error {
	for _, f := range files {
		for _, spec := range f.Imports {
			p, err := strconv.Unquote(spec.Path.Value)
			if err != nil {
				return fmt.Errorf("package %s: unreadable import path %s", importerPath, spec.Path.Value)
			}
			dir, isLocal := l.localDirFor(p)
			if !isLocal {
				// An ALLOWED LIBRARY package (stdlibsource.go) loads as a
				// source unit from the pinned GOROOT — once per program,
				// its own imports discovered recursively (allowed ones
				// become units too; everything else resolves to export
				// data for type-checking only, bodies absent).
				if _, allowed := stdlibSourceAllowed[p]; allowed {
					if _, seen := l.locals[p]; seen {
						continue
					}
					if l.libPin == nil {
						if err := checkStdlibSrcRev(); err != nil {
							return err
						}
						pin, err := loadStdlibPin()
						if err != nil {
							return err
						}
						l.libPin = pin
					}
					unit, err := l.parseLibrary(p, l.libPin)
					if err != nil {
						return err
					}
					l.locals[p] = unit
					if err := l.discover(p, unit.files); err != nil {
						return err
					}
					continue
				}
				// Not a case-local package: the stdlib importer is the
				// only other resolver, and IT reports unknown paths at
				// type-check (fail closed there, as before).
				continue
			}
			// cmd/go's import rules on the path and the module graph
			// (BUG-219; the file's header): before any parse of the
			// directory, as gc's loader judges them.
			if err := l.judgeLocalImport(importerPath, spec, p, dir); err != nil {
				return err
			}
			// Fail-closed register (design note §6):
			if l.isStdlib(p) {
				return unsup("import %q is BOTH a stdlib package and a case-local directory — shadowing is refused, rename the local package", p)
			}
			if strings.Contains(p, ".") {
				return unsup("dotted local import path %q: the TypeId key grammar reserves '.' for the name separator (design note §3) — vendor at a dot-free path", p)
			}
			if p == "main" {
				return unsup("local import path %q is reserved (the main package's qualifier)", p)
			}
			if spec.Name != nil && spec.Name.Name == "." {
				return unsup("dot import of local package %q (dot imports of source packages are not modeled)", p)
			}
			if seen, ok := l.locals[p]; ok {
				// gc checks the importer-dependent rules on EVERY import
				// edge («the rules depend on the code doing the
				// importing»): a unit first reached through an importer
				// the internal rule allows (`lib` importing
				// `lib/internal/x`) is still refused to one it does not
				// (the main package importing the same path; the lane's
				// probe g14, measured).
				if err := l.judgeLocalUnit(importerPath, spec, p, seen); err != nil {
					return err
				}
				continue
			}
			unit, err := l.parseLocal(p, dir)
			if err != nil {
				return err
			}
			// The rules that need the parsed unit (BUG-219: the internal
			// rule's importer test, the package-main rule).
			if err := l.judgeLocalUnit(importerPath, spec, p, unit); err != nil {
				return err
			}
			l.locals[p] = unit
			if err := l.discover(p, unit.files); err != nil {
				return err
			}
		}
	}
	return nil
}

// parseLocal parses one local package directory: gc's file set under
// the pinned target (fileselect.go selectPackageFiles, BUG-108 — the
// same selection the main package gets; an excluded `_extra.go` or
// `lib_arm64.go` in an imported package is never read either), in
// lexical filename order. E8 REALIZATION SITE: the imported-unit twin
// of main.go's — the go command's DIRECTORY-mode member of the spec's
// files-as-presented latitude; file-list-mode orders are not modeled
// (main.go run() has the full note; the realized order is recorded on
// the wire as program "fileOrder").
func (l *loader) parseLocal(path, dir string) (*sourcePkg, error) {
	files, err := selectPackageFiles(l.fset, dir)
	if err != nil {
		return nil, err
	}
	// The imported unit's module language version (modfile.go, BUG-109):
	// its nearest go.mod — the main package's, or a nested module's own.
	if err := refuseForeignModuleVersion(dir); err != nil {
		return nil, err
	}
	unit := &sourcePkg{path: path, files: files}
	// (The langversion.go build-constraint policy ran inside
	// selectPackageFiles — local packages are the same modeled fragment.)
	// E5 stdlib shims are PER UNIT (raft W4.0): a local package calling
	// an allowlisted stdlib function gets its own injected shim
	// declarations, before ITS type-check — exactly like the main
	// package's injection in main.go. Reserved-name collisions refuse
	// here, loudly. (raft's errors.New sentinels live in non-main
	// units, which is why main-only injection was not enough.)
	shimFile, err := injectStdlibShims(l.fset, unit.files)
	if err != nil {
		return nil, err
	}
	if shimFile != nil {
		unit.files = append(unit.files, shimFile)
	}
	return unit, nil
}

// importPathsOf lists EVERY import path declared by a parsed unit —
// local and non-local, named, blank and dot alike — sorted and
// deduplicated. Every one of them is a node of the program's
// initialization list (a blank import's whole purpose is its position
// in that list), so no import form is filtered out here.
func importPathsOf(files []*ast.File) []string {
	seen := map[string]bool{}
	for _, f := range files {
		for _, spec := range f.Imports {
			p, err := strconv.Unquote(spec.Path.Value)
			if err != nil {
				continue // already refused by discover
			}
			seen[p] = true
		}
	}
	out := make([]string, 0, len(seen))
	for p := range seen {
		out = append(out, p)
	}
	sort.Strings(out)
	return out
}

// localImportsOf lists the LOCAL import paths of a parsed unit (the
// subset of its imports that is type-checked from source), sorted and
// deduplicated. This is the TYPE-CHECK dependency order, not the
// initialization order — see specInitOrder for the latter.
func (l *loader) localImportsOf(files []*ast.File) []string {
	out := []string{}
	for _, p := range importPathsOf(files) {
		if _, isLocal := l.locals[p]; isLocal {
			out = append(out, p)
		}
	}
	return out
}

// sourceHasInitWork approximates cmd/compile's decision about whether
// a SOURCE package has residual initialization work — the `len(fns)`
// half of MakeTask's pruning test (inittask.go).
//
// gc's answer is "what survives cmd/compile/internal/staticinit". The
// frontend's answer is syntactic, over the AST plus go/types' constant
// folding:
//
//   - a `func init()` with a non-empty body is work (gc drops an
//     init function whose body is empty, so `func init() {}` is not);
//   - a package-scope variable initializer is work UNLESS go/types
//     assigned the expression a CONSTANT value.
//
// THE DIRECTION OF THE APPROXIMATION, honestly. staticinit folds
// strictly MORE than "is a constant": it also statically initializes
// composite literals of static elements, copies from other statically
// initialized globals, and addresses of globals. So the syntactic rule
// UNDER-PRUNES — it can call a package a node that gc pruned, never
// the reverse. Under-pruning is the direction that keeps a spurious
// EDGE, which can delay an importer past a package it should have
// beaten; it is a real divergence, not a safe one, and it is measured
// rather than assumed: the 120-seed randomized differential harness
// (artifacts/delta-review-probe/gen2.py) and the residual entry in
// docs/spec-divergence-ledger.md carry the count. It is chosen over a
// deeper staticinit port because the rule is legible and its failure
// mode is a wrong ORDER we can measure, whereas a half-ported
// staticinit's failure mode is a wrong order we would believe.
//
// Over-pruning — calling a package pruned that gc schedules — is what
// would be unsafe (it deletes a real edge), and the rule cannot do it
// through the `fns` half: a constant initializer generates no code and
// an empty init body is dropped by gc too.
//
// Since 2026-10-12 (the BUG-061 guard, [USER] ruling D1: refuse the case
// if excluding it is easy) the rule is computed by sourceInitWork
// (staticinit.go), which ALSO sorts the non-constant initializers into
// the shapes staticinit certainly leaves as work and the shapes it may
// fold. The node fact here is unchanged — "constant or nothing" prunes,
// anything else is a node; the second sort feeds only the refusal that
// fires when the uncertainty would change the order of the packages
// with work.
func (l *loader) sourceHasInitWork(u *sourcePkg) bool {
	certain, maybe := l.sourceInitWork(u)
	return certain || len(maybe) > 0
}

// initGraph is the program's initialization graph, in the LINKER
// SYMBOL PREFIX namespace (inittask.go): keys are
// objabi.PathToPrefix(importPath), which is what gc's edges name and
// what its tie-break sorts by.
type initGraph struct {
	deps map[string][]string   // prefix -> the prefixes it imports
	src  map[string]*sourcePkg // prefix -> source unit, for source packages
	node map[string]bool       // prefix -> is a node of gc's schedule
	work map[string]bool       // prefix -> has residual init work of its own
	// prefix -> the MAYBE-STATIC initializers of a source package whose
	// work is otherwise nil: the frontend counts it as work, gc may not
	// (BUG-061, staticinit.go). Empty for every certain package.
	uncertain map[string][]initSite
}

// specInitOrder returns ALL the source units in the order the program
// initializes them, computed as gc's schedule rather than the spec's
// literal reading (inittask.go documents the two divergences and why
// they are observable):
//
//  1. build the graph over the source units plus the transitive
//     closure of their non-source imports, edges from the import
//     DECLARATIONS (which is what cmd/compile's Target.Imports is);
//  2. compute the NODE set — a package is a node iff it has residual
//     init work of its own or an inittask-bearing import, to fixpoint;
//     stdlib node facts come from the generated table, source ones
//     from sourceHasInitWork;
//  3. walk the nodes: repeatedly take the lexicographically first
//     READY node BY SORT KEY (prefix + "..inittask");
//  4. emit the PRUNED source units first, then the scheduled ones in
//     walk order.
//
// Step 4 is not a fallback, it is the faithful placement. A pruned
// package's variable initializers are exactly the ones gc folded into
// the DATA SECTION: their values are in place before any init code
// runs anywhere in the program. And a pruned package can only hold
// constants, so nothing it assigns can depend on another package's
// run-time value — emitting the whole pruned set up front, in
// dependency order among themselves, reproduces "already initialized"
// without inventing a position in a schedule the package is not in.
//
// main is always a node (gc emits its record unconditionally) and is
// always last: every source unit is reachable from main by imports,
// and a chain ending at a node is all nodes, so no source node can be
// scheduled after main.
//
// A single source unit is returned unchanged without touching the
// import graph: with one package there is exactly one position to
// occupy. That keeps every single-package case (the overwhelming
// majority of the corpus) on exactly the old code path and cost.
func (l *loader) specInitOrder(units []*sourcePkg, mainUnit *sourcePkg) ([]*sourcePkg, error) {
	if len(units) < 2 {
		return units, nil
	}
	g, err := l.buildInitGraph(units, mainUnit)
	if err != nil {
		return nil, err
	}

	keys := make([]string, 0, len(g.deps))
	for p := range g.deps {
		keys = append(keys, p)
	}
	// The schedule's own key: the inittask SYMBOL name, not the path.
	sort.Slice(keys, func(i, j int) bool {
		return keys[i]+initTaskSuffix < keys[j]+initTaskSuffix
	})

	walk, err := walkInitSchedule(keys, g, g.node)
	if err != nil {
		return nil, err
	}
	// BUG-061 guard (staticinit.go): the walk above is emitted only if
	// no admissible pruning of the uncertain packages reorders the
	// packages with work.
	if err := l.checkStaticinitSensitivity(g, keys, walk); err != nil {
		return nil, err
	}
	out := make([]*sourcePkg, 0, len(units))
	for _, p := range walk {
		if u, isSrc := g.src[p]; isSrc {
			out = append(out, u)
		}
	}
	return out, nil
}

// walkInitSchedule runs the two-pass walk over keys (sorted by schedule
// key) for the given node set and returns every prefix in the order it
// is initialized. Pass 1 drains the PRUNED packages, pass 2 runs gc's
// schedule over the nodes. Pass 1 is closed under its own dependencies
// — a pruned package has no inittask-bearing import, so everything it
// imports is pruned too — which is also why the readiness test can stay
// "every import done" in both passes: by the time pass 2 starts, every
// pruned package is already done, so the only undone imports it can see
// are the node edges gc actually walks.
func walkInitSchedule(keys []string, g *initGraph, node map[string]bool) ([]string, error) {
	out := make([]string, 0, len(keys))
	done := map[string]bool{}
	for _, nodePass := range []bool{false, true} {
		remaining := 0
		for _, p := range keys {
			if node[p] == nodePass {
				remaining++
			}
		}
		for remaining > 0 {
			progressed := false
			for _, p := range keys {
				if done[p] || node[p] != nodePass {
					continue
				}
				ready := true
				for _, dep := range g.deps[p] {
					if !done[dep] {
						ready = false
						break
					}
				}
				if !ready {
					continue
				}
				done[p] = true
				remaining--
				progressed = true
				out = append(out, p)
				break // restart from the lexicographic front
			}
			if !progressed {
				blocked := []string{}
				for _, p := range keys {
					if !done[p] && node[p] == nodePass {
						blocked = append(blocked, p)
					}
				}
				return nil, unsup("import cycle in the program initialization schedule: %v", blocked)
			}
		}
	}
	return out, nil
}

// solveInitNodes computes the node set for a work assignment: a
// non-source package's node fact IS its table fact (work == node for
// those rows); a source package is a node iff it has work of its own
// or imports a node, to fixpoint. Only the SOURCE packages need
// solving — a stdlib package can never import a source one.
func solveInitNodes(g *initGraph, work map[string]bool) map[string]bool {
	node := map[string]bool{}
	for p := range g.deps {
		if _, isSrc := g.src[p]; !isSrc {
			node[p] = work[p]
		}
	}
	for changed := true; changed; {
		changed = false
		for prefix := range g.src {
			if node[prefix] {
				continue
			}
			isNode := work[prefix]
			if !isNode {
				for _, dep := range g.deps[prefix] {
					if node[dep] {
						isNode = true
						break
					}
				}
			}
			if isNode {
				node[prefix] = true
				changed = true
			}
		}
	}
	return node
}

// buildInitGraph closes over the program's imports and decides, for
// every package reached, whether gc schedules it.
func (l *loader) buildInitGraph(units []*sourcePkg, mainUnit *sourcePkg) (*initGraph, error) {
	g := &initGraph{
		deps:      map[string][]string{},
		src:       map[string]*sourcePkg{},
		node:      map[string]bool{},
		work:      map[string]bool{},
		uncertain: map[string][]initSite{},
	}
	// THE WORKLIST CARRIES LINKER SYMBOL PREFIXES, NEVER IMPORT PATHS
	// (BUG-064). Source imports are converted by pathToPrefix exactly
	// once, on push; the table's dep columns are ALREADY prefixes (gc's
	// R_INITORDER edges, read from the compiled archives) and go on the
	// worklist verbatim. The old code pushed both and re-escaped every
	// popped item, so an already-escaped prefix — the stdlib ships one,
	// crypto/internal/entropy/v1%2e0%2e0 — was escaped AGAIN ('%' ->
	// '%25') and the table lookup missed a row the table has, refusing
	// every multi-package program whose init closure reaches it
	// (crypto/rand and the rest of the crypto family; raft's route is
	// the election-jitter draw). display carries the import path where
	// one is known, for the refusal message only.
	type workItem struct{ prefix, display string }
	pending := []workItem{}
	for _, u := range units {
		prefix := pathToPrefix(u.path)
		if other, dup := g.src[prefix]; dup {
			return nil, unsup("source packages %q and %q share the linker symbol prefix %q, so the initialization schedule cannot tell them apart", other.path, u.path, prefix)
		}
		g.src[prefix] = u
		ds := []string{}
		for _, p := range importPathsOf(u.files) {
			ds = append(ds, pathToPrefix(p))
			pending = append(pending, workItem{prefix: pathToPrefix(p), display: p})
		}
		g.deps[prefix] = ds
		// cmd/compile emits main's record unconditionally, whether or
		// not it has any work of its own (MakeTask's pruning test
		// exempts `main` and `runtime` by name).
		//
		// A LIBRARY unit (stdlib source-through) takes its node fact
		// from the generated table — gc's OWN answer for that package,
		// read from the compiled archive — not from the syntactic
		// approximation: the package occupies exactly the schedule
		// position it had as an ordering-only placeholder (memo §6
		// mechanism 6; BUG-060/BUG-061 territory), and now its real
		// `$init` runs there. Its edges are its import declarations,
		// like every other source unit; non-node imports drain in pass 1
		// so the two edge sets agree on the walk.
		if u.library {
			entry, err := stdInitLookup(prefix, u.path)
			if err != nil {
				return nil, err
			}
			g.work[prefix] = entry.node
		} else if u == mainUnit {
			g.work[prefix] = true
		} else {
			// The node fact is sourceHasInitWork's, unchanged; the
			// MAYBE-STATIC sites of a package with no certain work are
			// what the BUG-061 guard enumerates over (staticinit.go).
			certain, maybe := l.sourceInitWork(u)
			g.work[prefix] = certain || len(maybe) > 0
			if !certain && len(maybe) > 0 {
				g.uncertain[prefix] = maybe
			}
		}
	}
	// Close over the non-source packages, taking their node facts and
	// their edges from the generated table — gc's own answers, read
	// out of the compiled archives (inittask.go).
	for len(pending) > 0 {
		item := pending[0]
		pending = pending[1:]
		if _, seen := g.deps[item.prefix]; seen {
			continue
		}
		if _, isSrc := g.src[item.prefix]; isSrc {
			continue
		}
		entry, err := stdInitLookup(item.prefix, item.display)
		if err != nil {
			return nil, err
		}
		g.deps[item.prefix] = entry.deps
		g.node[item.prefix] = entry.node
		g.work[item.prefix] = entry.node
		for _, dep := range entry.deps {
			// A table dep is a PREFIX (never a path — handing it to
			// pathToPrefix would double-escape it: BUG-064). Column 4
			// of the table carries the unescaped path for the rows
			// where the two differ, so refusal messages can name the
			// package the way it is written in source; stdInitDisplay
			// falls back to the prefix for every other row.
			pending = append(pending, workItem{prefix: dep, display: stdInitDisplay(dep)})
		}
	}
	// Node set to fixpoint: a package is a node iff it has work of its
	// own or imports a node (solveInitNodes; the table already gives the
	// closed answer for the non-source rows).
	g.node = solveInitNodes(g, g.work)
	return g, nil
}

// chainedImporter resolves local packages from the loader's checked
// set first, then falls through to the stdlib importer. types.Config
// calls it for every import during Check.
type chainedImporter struct {
	locals map[string]*sourcePkg
	stdlib types.Importer
}

func (c *chainedImporter) Import(path string) (*types.Package, error) {
	if unit, ok := c.locals[path]; ok {
		if unit.pkg == nil {
			// Dependency order guarantees a checked package; reaching
			// this is a loader bug OR an import cycle go/types is
			// probing — refuse rather than recurse.
			return nil, fmt.Errorf("local package %s not yet type-checked (import cycle?)", path)
		}
		return unit.pkg, nil
	}
	return c.stdlib.Import(path)
}

// loadProgram parses + type-checks the whole program: the main
// package in mainFiles plus every transitively imported local
// package. The main unit's path is its declared package NAME —
// exactly the path the pre-multi-package frontend passed to Check, so
// single-package wires are byte-identical (path == name ⇒ unchanged
// qualifiers). Returns the units in PROGRAM INITIALIZATION ORDER
// (spec §Package initialization, Go 1.21+: repeatedly initialize the
// lexicographically first uninitialized package whose imports are all
// initialized; main — everything's importer — lands last).
func loadProgram(fset *token.FileSet, rootDir string, mainFiles []*ast.File) ([]*sourcePkg, error) {
	return newLoader(fset, rootDir).loadProgram(mainFiles)
}

// loadProgram is the method form of the function above, on a fresh
// loader; tests that need the loader afterwards (the BUG-061
// classifier's unit tests) call it directly.
func (l *loader) loadProgram(mainFiles []*ast.File) ([]*sourcePkg, error) {
	if len(mainFiles) == 0 {
		return nil, fmt.Errorf("no Go files in %s", l.rootDir)
	}
	mainName := mainFiles[0].Name.Name
	l.mainName = mainName
	// The module governing the lowered directory (BUG-217, BUG-219): its
	// path's meaning for the main package is judged first, and its graph
	// is what a case-local import must resolve through in discover.
	mod, err := moduleFor(l.rootDir)
	if err != nil {
		return nil, err
	}
	l.mod = mod
	if mod != nil {
		if err := refuseReservedModulePath(l.rootDir, mod); err != nil {
			return nil, err
		}
	}
	if err := l.discover(mainName, mainFiles); err != nil {
		return nil, err
	}
	if _, collides := l.locals[mainName]; collides {
		return nil, unsup("local import path %q collides with the main package's qualifier", mainName)
	}

	mainUnit := &sourcePkg{path: mainName, files: mainFiles}
	l.mainUnit = mainUnit
	l.locals[mainName] = mainUnit // for edge computation only; removed below
	for _, unit := range l.locals {
		unit.localImports = l.localImportsOf(unit.files)
	}
	delete(l.locals, mainName)

	// TYPE-CHECK order over the local units + main: any dependency
	// order will do (go/types needs each unit's imports checked before
	// it), and the lexicographic-first-ready walk is one. This is NOT
	// the initialization order — specInitOrder below computes that over
	// the complete program's package list, once type-checking has
	// resolved every import. Cycles refuse here first.
	order := []*sourcePkg{}
	done := map[string]bool{}
	units := map[string]*sourcePkg{mainName: mainUnit}
	names := []string{}
	for p, u := range l.locals {
		units[p] = u
	}
	for p := range units {
		names = append(names, p)
	}
	sort.Strings(names)
	for len(order) < len(names) {
		progressed := false
		for _, p := range names {
			if done[p] {
				continue
			}
			ready := true
			for _, dep := range units[p].localImports {
				if !done[dep] {
					ready = false
					break
				}
			}
			if ready {
				order = append(order, units[p])
				done[p] = true
				progressed = true
				break // restart from the lexicographic front
			}
		}
		if !progressed {
			blocked := []string{}
			for _, p := range names {
				if !done[p] {
					blocked = append(blocked, p)
				}
			}
			return nil, unsup("import cycle among local packages: %v", blocked)
		}
	}

	// Type-check in dependency order (the same order works: every
	// unit's imports precede it). GoVersion is the PINNED language
	// version (langversion.go): unset, go/types disables version
	// checking entirely — the ambient-toolchain fail-open p2 claim 3
	// measured.
	lang, err := pinnedLangVersion()
	if err != nil {
		return nil, err
	}
	imp := &chainedImporter{locals: l.locals, stdlib: l.stdlib}
	for _, unit := range order {
		unit.info = newTypesInfo()
		conf := types.Config{Importer: imp, GoVersion: lang}
		pkg, err := conf.Check(unit.path, l.fset, unit.files, unit.info)
		if err != nil {
			return nil, fmt.Errorf("type-check: %w", err)
		}
		unit.pkg = pkg
	}
	if err := checkEntryDeclared(l.rootDir, mainUnit); err != nil { // entrymode.go, BUG-125
		return nil, err
	}
	if err := checkEntryReferenced(l.fset, mainUnit); err != nil { // entrymode.go, BUG-220
		return nil, err
	}

	// gc's type-size limits (gclimits.go, release-readiness row 34): a
	// whole-program, type-check-class rejection — gc rejects the
	// compilation unit, so nothing may lower.
	if err := checkGcSizeLimits(l.fset, order); err != nil {
		return nil, err
	}

	// Reachability pruning of the LIBRARY units (stdlibreach.go): from
	// the program's roots (every declaration of every non-library unit,
	// plus the library units' own init() functions and effectful
	// package-variable initializers), the set of library declarations
	// that lower. Computed once, over the type-checked program.
	if err := computeLibraryReach(order); err != nil {
		return nil, err
	}

	// The per-initializer classification the E7 detector reads
	// (hiddendep.go; staticinit.go initKindsOf) — over every unit,
	// library units included, once the whole program is type-checked.
	for _, u := range order {
		u.initKinds = l.initKindsOf(u)
	}

	// gc's schedule, over the PRUNED node set (inittask.go).
	initOrder, err := l.specInitOrder(order, mainUnit)
	if err != nil {
		return nil, err
	}
	if len(initOrder) != len(order) {
		return nil, unsup("initialization list dropped %d source package(s)", len(order)-len(initOrder))
	}
	// main imports every other source package transitively (they are
	// discovered from its imports), so it can only be initialized last.
	// The emitter relies on that (main.go takes units[len-1] as the main
	// unit), so check it rather than assume it.
	if last := initOrder[len(initOrder)-1]; last != mainUnit {
		return nil, unsup("initialization list ends at %q, not the main package %q", last.path, mainName)
	}
	return initOrder, nil
}

// rejectImport is a `type-check`-class refusal at an import's position with
// gc's reason: the class the negative runner reads for gc's rejections of
// a program's source (the file's header on the class choice).
func (l *loader) rejectImport(spec *ast.ImportSpec, format string, args ...any) error {
	return fmt.Errorf("type-check: %s: %s", l.fset.Position(spec.Pos()), fmt.Sprintf(format, args...))
}

// findVendorElem mirrors cmd/go's FindVendor: the index of the last
// NON-TERMINATING `vendor` element (`x/vendor` is its own package).
func findVendorElem(path string) (int, bool) {
	switch {
	case strings.Contains(path, "/vendor/"):
		return strings.LastIndex(path, "/vendor/") + 1, true
	case strings.HasPrefix(path, "vendor/"):
		return 0, true
	}
	return 0, false
}

// findInternalElem mirrors cmd/go's findInternal: the index of the final
// `internal` element, at the start, in the middle or at the end.
func findInternalElem(path string) (int, bool) {
	switch {
	case strings.HasSuffix(path, "/internal"):
		return len(path) - len("internal"), true
	case strings.Contains(path, "/internal/"):
		return strings.LastIndex(path, "/internal/") + 1, true
	case path == "internal", strings.HasPrefix(path, "internal/"):
		return 0, true
	}
	return 0, false
}

// hasPathPrefix mirrors cmd/go's str.HasPathPrefix: s begins with the
// slash-separated elements of prefix (the empty prefix is every path's).
func hasPathPrefix(s, prefix string) bool {
	return prefix == "" || s == prefix || strings.HasPrefix(s, prefix+"/")
}

// importerImportPath is the import path gc gives the importing package:
// in GOPATH mode "" for the main package (it is outside GOPATH/src, and
// outside every internal/vendor tree) and the case-local path for a local
// unit; in module mode the main module's path plus the lowered directory
// (modload's DirImportPath) for the main package, the require path for a
// replaced case-local module.
func (l *loader) importerImportPath(importerPath string) (string, error) {
	if importerPath != l.mainName {
		return importerPath, nil
	}
	if l.mod == nil {
		return "", nil
	}
	return mainPackagePath(l.rootDir, l.mod)
}

// judgeLocalImport applies the rules that need only the import path and
// the module graph (the file's header: (a), (V), (M)) to a case-local
// import p at dir, imported by importerPath.
func (l *loader) judgeLocalImport(importerPath string, spec *ast.ImportSpec, p, dir string) error {
	// (V) the vendor text rule, both modes — gc's text differs by mode:
	// in GOPATH mode the visibility rule speaks first (the importer is
	// outside the vendor tree), in module mode the path rule.
	if i, ok := findVendorElem(p); ok {
		if l.mod == nil {
			return l.rejectImport(spec, "use of vendored package not allowed — gc's rule for an import path with a vendor element (cmd/go disallowVendorVisibility): the importing package is outside the tree that vendors %q; a vendored package is imported by its path after vendor/ (%q)", p, p[i+len("vendor/"):])
		}
		return l.rejectImport(spec, "%s must be imported as %s — gc's rule for an import path with a vendor element (cmd/go disallowVendor)", p, p[i+len("vendor/"):])
	}
	if l.mod == nil {
		// (a) GOPATH mode: a directory under GOROOT/src takes the import
		// before GOPATH is searched (go/build Import), Go files or not.
		if isDir, hasGo := gorootSrcDir(p); isDir {
			if hasGo {
				return unsup("import %q is BOTH a stdlib package and a case-local directory (GOROOT/src/%s holds Go files, which is go/build's test; in GOPATH mode gc resolves the import to GOROOT, never to the case-local directory) — shadowing is refused, rename the local package", p, p)
			}
			return l.rejectImport(spec, "import %q: no Go files in GOROOT/src/%s — in GOPATH mode gc resolves an import whose directory exists under GOROOT/src to GOROOT before GOPATH (go/build Import), and that directory holds no Go files; the case-local directory is never read", p, p)
		}
		return nil
	}
	// (M) module mode: the main module's graph must provide p — a
	// require plus a replace onto the case-local directory, which must be
	// a module of its own (its go.mod); the vendor directory rule beside it.
	versions := l.mod.requires[p]
	var rep *modReplace
	for i := range l.mod.replaces {
		r := &l.mod.replaces[i]
		if r.oldPath != p {
			continue
		}
		if r.oldVersion != "" && !slices.Contains(versions, r.oldVersion) {
			continue // a replace of a version the module does not require is inert
		}
		rep = r
		break
	}
	switch {
	case len(versions) == 0 && rep == nil:
		if isStandardImportPath(p) {
			return l.rejectImport(spec, "package %s is not in std (%s) — in module mode a dotless import path is a standard-library package or one a required module provides, and the main module (%s, %s) requires none for it; the case-local directory %s is not read by gc", p, filepath.Join(pinnedBuildContext().GOROOT, "src", filepath.FromSlash(p)), l.mod.module, l.mod.path, dir)
		}
		return l.rejectImport(spec, "no required module provides package %s — the main module (%s, %s) requires none for it; the case-local directory %s is not read by gc in module mode", p, l.mod.module, l.mod.path, dir)
	case rep == nil:
		return l.rejectImport(spec, "missing go.sum entry for module providing package %s (imported by %s) — the main module requires %s but replaces it with no directory, so gc would fetch it (the apparatus runs GOPROXY=off; a fetched module is not the case-local directory %s in any case)", p, l.mod.module, p, dir)
	case len(versions) == 0:
		return l.rejectImport(spec, "module %s provides package %s and is replaced but not required — gc's rule: a replace alone adds nothing to the build list (the main module %s, %s)", p, p, l.mod.module, l.mod.path)
	}
	if rep.newVersion != "" {
		return unsup("import %q: the main module (%s) replaces %s with the module %s %s, not a directory — the lowering reads case-local directories only; refuse by name (fail closed)", p, l.mod.path, p, rep.newPath, rep.newVersion)
	}
	target := rep.newPath
	if !filepath.IsAbs(target) {
		target = filepath.Join(l.mod.dir, filepath.FromSlash(target))
	}
	absTarget, err1 := filepath.Abs(target)
	absDir, err2 := filepath.Abs(dir)
	if err1 != nil || err2 != nil {
		return unsup("import %q: cannot resolve the replacement directory %s against %s (%v, %v; fail closed)", p, rep.newPath, dir, err1, err2)
	}
	if filepath.Clean(absTarget) != filepath.Clean(absDir) {
		return unsup("import %q: the main module (%s) replaces %s with the directory %s, which is not the case-local directory %s — gc builds the replacement and this lowering reads case-local directories only; refuse by name (fail closed)", p, l.mod.path, p, rep.newPath, dir)
	}
	if fi, err := os.Stat(filepath.Join(dir, "go.mod")); err != nil || fi.IsDir() {
		return l.rejectImport(spec, "module %s: reading %s: no such file or directory — gc requires a replacement directory to be a module (its own go.mod)", rep.newPath, filepath.Join(filepath.FromSlash(p), "go.mod"))
	}
	if fi, err := os.Stat(filepath.Join(l.mod.dir, "vendor")); err == nil && fi.IsDir() {
		return modRefuse("%s has a vendor directory beside the module root and the program imports the replaced module %s — with a go version of 1.14 or later gc builds such a module in VENDOR mode (-mod=vendor by default), reading vendor/modules.txt and the vendor tree instead of the replacement directory (without the file it refuses: «inconsistent vendoring», measured); vendor mode is not modeled; refuse by name (fail closed)", l.mod.path, p)
	}
	return nil
}

// judgeLocalUnit applies the rules that need the parsed unit (the file's
// header: (I), (P)) to a case-local import p imported by importerPath.
func (l *loader) judgeLocalUnit(importerPath string, spec *ast.ImportSpec, p string, unit *sourcePkg) error {
	// (I) the internal rule: the importer must be inside the tree rooted
	// at the parent of the final `internal` element — by directory in
	// GOPATH mode (the main package, outside GOPATH/src, is inside none;
	// a case-local importer Q at GOPATH/src/Q is inside GOPATH/src/parent
	// iff Q has the path prefix), by import path in module mode.
	if i, ok := findInternalElem(p); ok {
		if i > 0 {
			i-- // rewind over the slash in ".../internal"
		}
		parent := p[:i]
		importer, err := l.importerImportPath(importerPath)
		if err != nil {
			return err
		}
		allowed := hasPathPrefix(importer, parent)
		if l.mod == nil && importerPath == l.mainName {
			allowed = false // the main package is outside every tree under GOPATH/src
		}
		if !allowed {
			return l.rejectImport(spec, "use of internal package %s not allowed — gc's rule (golang.org/s/go14internal, cmd/go disallowInternal): the importing package (%s) is outside the tree rooted at the parent of internal (%q)", p, importerDisplay(importerPath, l.mainName), parent)
		}
	}
	// (P) a program is not importable.
	if len(unit.files) > 0 && unit.files[0].Name.Name == "main" {
		return l.rejectImport(spec, "import %q is a program, not an importable package — gc's rule (cmd/go loadImport): the directory's package clause is main", p)
	}
	return nil
}

func importerDisplay(importerPath, mainName string) string {
	if importerPath == mainName {
		return "the main package"
	}
	return importerPath
}
