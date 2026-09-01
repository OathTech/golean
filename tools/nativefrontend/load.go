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
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
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
				// Not a case-local package: the stdlib importer is the
				// only other resolver, and IT reports unknown paths at
				// type-check (fail closed there, as before).
				continue
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
			if _, seen := l.locals[p]; seen {
				continue
			}
			unit, err := l.parseLocal(p, dir)
			if err != nil {
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

// parseLocal parses one local package directory (non-test files,
// lexical filename order — the same presentation order the main
// package gets). E8 REALIZATION SITE: the sort below is the imported-
// unit twin of main.go's — the go command's DIRECTORY-mode member of
// the spec's files-as-presented latitude; file-list-mode orders are
// not modeled (main.go run() has the full note; the realized order is
// recorded on the wire as program "fileOrder").
func (l *loader) parseLocal(path, dir string) (*sourcePkg, error) {
	pkgs, err := parser.ParseDir(l.fset, dir, nonTestGoFile, parser.ParseComments)
	if err != nil {
		return nil, err
	}
	if len(pkgs) != 1 {
		return nil, fmt.Errorf("expected exactly one package in %s, found %d", dir, len(pkgs))
	}
	unit := &sourcePkg{path: path}
	for _, pkg := range pkgs {
		paths := make([]string, 0, len(pkg.Files))
		for p := range pkg.Files {
			paths = append(paths, p)
		}
		sort.Strings(paths)
		for _, p := range paths {
			unit.files = append(unit.files, pkg.Files[p])
		}
	}
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
func sourceHasInitWork(u *sourcePkg) bool {
	for _, f := range u.files {
		for _, decl := range f.Decls {
			switch d := decl.(type) {
			case *ast.FuncDecl:
				if d.Recv == nil && d.Name.Name == "init" && d.Body != nil && len(d.Body.List) > 0 {
					return true
				}
			case *ast.GenDecl:
				if d.Tok != token.VAR {
					continue
				}
				for _, spec := range d.Specs {
					vs, ok := spec.(*ast.ValueSpec)
					if !ok {
						continue
					}
					for _, value := range vs.Values {
						// No recorded constant value => the
						// initializer runs at initialization time.
						// An expression go/types never typed (it
						// should not exist after a clean Check) is
						// treated as work: fail towards a node.
						if tv, typed := u.info.Types[value]; !typed || tv.Value == nil {
							return true
						}
					}
				}
			}
		}
	}
	return false
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

	out := make([]*sourcePkg, 0, len(units))
	done := map[string]bool{}
	// Pass 1 drains the PRUNED packages, pass 2 runs gc's schedule
	// over the nodes. Pass 1 is closed under its own dependencies — a
	// pruned package has no inittask-bearing import, so everything it
	// imports is pruned too — which is also why the readiness test can
	// stay "every import done" in both passes: by the time pass 2
	// starts, every pruned package is already done, so the only
	// undone imports it can see are the node edges gc actually walks.
	for _, nodePass := range []bool{false, true} {
		remaining := 0
		for _, p := range keys {
			if g.node[p] == nodePass {
				remaining++
			}
		}
		for remaining > 0 {
			progressed := false
			for _, p := range keys {
				if done[p] || g.node[p] != nodePass {
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
				if u, isSrc := g.src[p]; isSrc {
					out = append(out, u)
				}
				break // restart from the lexicographic front
			}
			if !progressed {
				blocked := []string{}
				for _, p := range keys {
					if !done[p] && g.node[p] == nodePass {
						blocked = append(blocked, p)
					}
				}
				return nil, unsup("import cycle in the program initialization schedule: %v", blocked)
			}
		}
	}
	return out, nil
}

// buildInitGraph closes over the program's imports and decides, for
// every package reached, whether gc schedules it.
func (l *loader) buildInitGraph(units []*sourcePkg, mainUnit *sourcePkg) (*initGraph, error) {
	g := &initGraph{
		deps: map[string][]string{},
		src:  map[string]*sourcePkg{},
		node: map[string]bool{},
		work: map[string]bool{},
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
		g.work[prefix] = u == mainUnit || sourceHasInitWork(u)
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
	// own or imports a node. Only the SOURCE packages need solving —
	// the table already gives the closed answer for the rest, and a
	// stdlib package can never import a source one.
	for changed := true; changed; {
		changed = false
		for prefix := range g.src {
			if g.node[prefix] {
				continue
			}
			isNode := g.work[prefix]
			if !isNode {
				for _, dep := range g.deps[prefix] {
					if g.node[dep] {
						isNode = true
						break
					}
				}
			}
			if isNode {
				g.node[prefix] = true
				changed = true
			}
		}
	}
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
	if len(mainFiles) == 0 {
		return nil, fmt.Errorf("no Go files in %s", rootDir)
	}
	mainName := mainFiles[0].Name.Name
	l := newLoader(fset, rootDir)
	if err := l.discover(mainName, mainFiles); err != nil {
		return nil, err
	}
	if _, collides := l.locals[mainName]; collides {
		return nil, unsup("local import path %q collides with the main package's qualifier", mainName)
	}

	mainUnit := &sourcePkg{path: mainName, files: mainFiles}
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
	// unit's imports precede it).
	imp := &chainedImporter{locals: l.locals, stdlib: l.stdlib}
	for _, unit := range order {
		unit.info = newTypesInfo()
		conf := types.Config{Importer: imp}
		pkg, err := conf.Check(unit.path, fset, unit.files, unit.info)
		if err != nil {
			return nil, fmt.Errorf("type-check: %w", err)
		}
		unit.pkg = pkg
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
