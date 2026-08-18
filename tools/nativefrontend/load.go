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
// PROGRAM INITIALIZATION ORDER (design note §5; audit F1). The schedule
// is spec#Program_initialization: "Given the list of all packages,
// sorted by import path, in each step the first uninitialized package
// in the list for which all imported packages (if any) are already
// initialized is initialized." The list is the COMPLETE PROGRAM's —
// spec#Program_execution: main "with all the packages it imports,
// transitively" — so the imported stdlib packages are nodes in it,
// whether or not we model them. specInitOrder therefore builds the
// list over ALL packages: the source units plus the transitive closure
// of every non-source import. Stdlib packages OCCUPY POSITIONS in the
// schedule and contribute NO emitted initializer (their bodies are not
// modeled); only their ORDERING EFFECT lands, and that is computable
// from the import graph alone. Dropping them is NOT conservative: a
// source package gated by a stdlib import becomes ready too early and
// can be scheduled ahead of a lexicographically later package that is
// genuinely ready (BUG-060, pinned by multipkg/init-order-stdlib).

import (
	"fmt"
	"go/ast"
	"go/build"
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
	// Import paths of the LOCAL packages this package imports
	// (initialization-order edges).
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
	// Import declarations of the NON-source packages reached while
	// building the initialization list, by import path (see nonSrcDeps).
	nonSrcCache map[string][]string
}

func newLoader(fset *token.FileSet, rootDir string) *loader {
	return &loader{
		fset:        fset,
		rootDir:     rootDir,
		locals:      map[string]*sourcePkg{},
		stdlib:      importer.Default(),
		stdlibProbe: map[string]bool{},
		nonSrcCache: map[string][]string{},
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
// package gets).
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

// nonSrcDeps returns the import declarations of a package we do NOT
// have source for — i.e. a stdlib package pulled into the program's
// initialization list by some source package's import.
//
// It reads them with go/build, which reports the package's actual
// import CLAUSES (build-constraint-filtered for the host toolchain,
// exactly as the oracle's `go run` resolves them on the same host).
// Deliberately NOT types.Package.Imports(): export data records the
// packages whose objects the compiler referenced, which is neither a
// subset nor a superset of the import declarations the spec's ordering
// ranges over — measured at Go 1.26, `sync`'s export data lists
// internal/abi (which sync does not import) and omits runtime (which
// it does). Fail closed: a path go/build cannot resolve refuses the
// export rather than being treated as a leaf, since a missing edge
// silently perturbs the schedule.
func (l *loader) nonSrcDeps(path string) ([]string, error) {
	if ds, ok := l.nonSrcCache[path]; ok {
		return ds, nil
	}
	bp, err := build.Default.Import(path, "", 0)
	if err != nil {
		return nil, unsup("cannot resolve imported package %q while building the program initialization list (spec#Program_initialization ranges over ALL packages of the complete program): %v", path, err)
	}
	ds := append([]string(nil), bp.Imports...)
	sort.Strings(ds)
	l.nonSrcCache[path] = ds
	return ds, nil
}

// specInitOrder returns the SOURCE units in the program initialization
// order of spec#Program_initialization, computed over the complete
// program's package list: the source units plus the transitive closure
// of their non-source (stdlib) imports. The non-source packages take
// their positions in the schedule and are then dropped from the result
// — they contribute no emitted initializer, only the ordering effect
// of standing between a source package and its readiness.
//
// A single source unit is returned unchanged without touching the
// import graph: with one package there is exactly one position to
// occupy, so the schedule is fixed whatever the rest of the list looks
// like. That keeps every single-package case (the overwhelming
// majority of the corpus) on exactly the old code path and cost.
func (l *loader) specInitOrder(units []*sourcePkg) ([]*sourcePkg, error) {
	if len(units) < 2 {
		return units, nil
	}
	src := map[string]*sourcePkg{}
	deps := map[string][]string{}
	pending := []string{}
	for _, u := range units {
		src[u.path] = u
		ds := importPathsOf(u.files)
		deps[u.path] = ds
		pending = append(pending, ds...)
	}
	// Close over the non-source packages the source units reach.
	for len(pending) > 0 {
		p := pending[0]
		pending = pending[1:]
		if _, seen := deps[p]; seen {
			continue
		}
		ds, err := l.nonSrcDeps(p)
		if err != nil {
			return nil, err
		}
		deps[p] = ds
		pending = append(pending, ds...)
	}

	names := make([]string, 0, len(deps))
	for p := range deps {
		names = append(names, p)
	}
	sort.Strings(names)

	out := make([]*sourcePkg, 0, len(units))
	done := map[string]bool{}
	for len(done) < len(names) {
		progressed := false
		for _, p := range names {
			if done[p] {
				continue
			}
			ready := true
			for _, dep := range deps[p] {
				if !done[dep] {
					ready = false
					break
				}
			}
			if !ready {
				continue
			}
			done[p] = true
			progressed = true
			if u, isSrc := src[p]; isSrc {
				out = append(out, u)
			}
			break // restart from the lexicographic front
		}
		if !progressed {
			blocked := []string{}
			for _, p := range names {
				if !done[p] {
					blocked = append(blocked, p)
				}
			}
			return nil, unsup("import cycle in the program initialization list: %v", blocked)
		}
	}
	return out, nil
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

	// The spec's schedule, over ALL packages of the complete program.
	initOrder, err := l.specInitOrder(order)
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
