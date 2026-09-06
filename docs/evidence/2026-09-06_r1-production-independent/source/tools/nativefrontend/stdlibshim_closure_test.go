package main

// Closure tests for the E5 stdlib-shim INJECTION plumbing
// (stdlibshim.go, injectStdlibShims). BUG-086 (noodler lane,
// 2026-09-03): a program calling strconv.FormatInt WITHOUT
// strconv.FormatUint had FormatInt's shim SOURCE planted but not the
// FormatUint shim it calls, and the export died in the type-checker
// (`undefined: goleanShimStrconvFormatUint`) — a whole-program spurious
// refusal of an ALLOWLISTED member. Nothing expressed "shim A's source
// depends on shim B's source". These tests mechanize the property that
// bug violated, once for every entry of every call-shape table: the
// bundle a single call plants must type-check STANDING ALONE.
//
// D-002 (docs/discrepancy-backlog.md): the injection surface is frozen.
// These tests add no shim and change no body; they check the plumbing.

import (
	"fmt"
	"go/ast"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"sort"
	"strings"
	"testing"
)

// shimProbe is one call-shape-table entry rendered as the smallest
// program whose SYNTACTIC scan (injectStdlibShims is pre-type-check)
// marks exactly that entry's shims as needed. The call carries no
// arguments: the user file is never type-checked here — only the
// injected shim file is, standing alone.
type shimProbe struct {
	label string // "pkg.Sel" (or "pkg.Var.Method")
	src   string
}

// allShimProbes enumerates EVERY entry of the four injection tables
// (direct allowlist, generic desugar, fmt desugar, package-variable
// method), sorted by label so a failure names a stable row.
func allShimProbes() []shimProbe {
	var probes []shimProbe
	add := func(path, local, callee string) {
		probes = append(probes, shimProbe{
			label: local + "." + callee,
			src: fmt.Sprintf("package main\n\nimport %q\n\nfunc main() {\n\t%s.%s()\n}\n",
				path, local, callee),
		})
	}
	localOf := func(path string) string {
		if i := lastSlash(path); i >= 0 {
			return path[i+1:]
		}
		return path
	}
	for path, fns := range stdlibShimAllowlist {
		for sel := range fns {
			add(path, localOf(path), sel)
		}
	}
	for path, fns := range stdlibDesugarInject {
		for sel := range fns {
			add(path, localOf(path), sel)
		}
	}
	for path, fns := range stdlibGenericDesugarInject {
		for sel := range fns {
			add(path, localOf(path), sel)
		}
	}
	sort.Slice(probes, func(i, j int) bool { return probes[i].label < probes[j].label })
	return probes
}

// typeCheckShimFileAlone type-checks an injected shim file as a
// one-file package and returns EVERY error go/types reports (not just
// the first): a bundle that is not closed under its own references
// fails here with `undefined: <name>` for each missing declaration.
func typeCheckShimFileAlone(t *testing.T, fset *token.FileSet, shimFile *ast.File) []string {
	t.Helper()
	lang, err := pinnedLangVersion()
	if err != nil {
		t.Fatalf("pinned language version: %v", err)
	}
	var errs []string
	conf := types.Config{
		Importer:  importer.Default(),
		GoVersion: lang,
		Error:     func(e error) { errs = append(errs, e.Error()) },
	}
	_, _ = conf.Check("main", fset, []*ast.File{shimFile}, nil)
	return errs
}

// injectForSource parses one user file and runs the real injection
// scan over it, returning the synthetic shim file (nil when nothing is
// needed — which is itself a failure for a table entry: the scan must
// see every entry it lists).
func injectForSource(t *testing.T, label, src string) (*token.FileSet, *ast.File) {
	t.Helper()
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "main.go", src, parser.ParseComments)
	if err != nil {
		t.Fatalf("%s: probe program failed to parse: %v\n%s", label, err, src)
	}
	shimFile, err := injectStdlibShims(fset, []*ast.File{f})
	if err != nil {
		t.Fatalf("%s: injectStdlibShims refused: %v", label, err)
	}
	if shimFile == nil {
		t.Fatalf("%s: injection scan planted NOTHING for a listed entry", label)
	}
	return fset, shimFile
}

// TestStdlibShimInjectionClosedPerEntry: for every call-shape-table
// entry, the bundle a call to that entry ALONE plants must type-check
// standing alone. This is the test that would have caught BUG-086
// (red on the pre-fix plumbing at exactly strconv.FormatInt; green
// once injection is dependency-closed).
func TestStdlibShimInjectionClosedPerEntry(t *testing.T) {
	probes := allShimProbes()
	if len(probes) == 0 {
		t.Fatal("no injection-table entries enumerated — the tables moved; fix the enumeration")
	}
	t.Logf("%d call-shape-table entries enumerated", len(probes))
	var failed []string
	for _, p := range probes {
		fset, shimFile := injectForSource(t, p.label, p.src)
		if errs := typeCheckShimFileAlone(t, fset, shimFile); len(errs) > 0 {
			failed = append(failed, p.label)
			t.Errorf("%s: injected shim bundle does NOT type-check alone (%d error(s)):\n  %s",
				p.label, len(errs), strings.Join(errs, "\n  "))
		}
	}
	if len(failed) > 0 {
		t.Errorf("unclosed entries: %v (of %d)", failed, len(probes))
	}
}

// shimNameOwner maps every reserved top-level name a shim declares
// (stdlibShimDeclNames) to the shim key that declares it.
func shimNameOwner(t *testing.T) map[string]string {
	t.Helper()
	owner := map[string]string{}
	for key, names := range stdlibShimDeclNames {
		for _, n := range names {
			if prev, dup := owner[n]; dup {
				t.Fatalf("reserved name %s declared by two shim keys (%s, %s)", n, prev, key)
			}
			owner[n] = key
		}
	}
	return owner
}

// shimSourceRefs returns the set of shim keys whose declared names a
// shim's SOURCE references as identifiers (comments excluded — the
// scan is over the parsed AST, not the text), minus the key itself.
func shimSourceRefs(t *testing.T, key string, owner map[string]string) map[string]bool {
	t.Helper()
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, key+".go", "package main\n"+stdlibShimSources[key], 0)
	if err != nil {
		t.Fatalf("%s: shim source failed to parse: %v", key, err)
	}
	refs := map[string]bool{}
	ast.Inspect(f, func(n ast.Node) bool {
		id, ok := n.(*ast.Ident)
		if !ok {
			return true
		}
		if o, reserved := owner[id.Name]; reserved && o != key {
			refs[o] = true
		}
		return true
	})
	return refs
}

// shimSourceDecls returns every top-level name a shim source declares:
// funcs, types, and methods by their receiver's base type (which must
// itself be declared in the same source). A shim source must declare
// NO package-level var or const: an injected declaration can never add
// a package-initialization entry to the user's program.
func shimSourceDecls(t *testing.T, key string) map[string]bool {
	t.Helper()
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, key+".go", "package main\n"+stdlibShimSources[key], 0)
	if err != nil {
		t.Fatalf("%s: shim source failed to parse: %v", key, err)
	}
	names := map[string]bool{}
	var methodOwners []string
	for _, decl := range f.Decls {
		switch d := decl.(type) {
		case *ast.FuncDecl:
			if d.Recv == nil {
				names[d.Name.Name] = true
				continue
			}
			rt := d.Recv.List[0].Type
			if star, ok := rt.(*ast.StarExpr); ok {
				rt = star.X
			}
			id, ok := rt.(*ast.Ident)
			if !ok {
				t.Errorf("%s: method %s has a non-identifier receiver type", key, d.Name.Name)
				continue
			}
			methodOwners = append(methodOwners, id.Name)
		case *ast.GenDecl:
			for _, spec := range d.Specs {
				switch s := spec.(type) {
				case *ast.TypeSpec:
					names[s.Name.Name] = true
				case *ast.ValueSpec:
					for _, id := range s.Names {
						t.Errorf("%s: declares package-level var/const %s — an injected shim must add no init entry", key, id.Name)
					}
				}
			}
		}
	}
	for _, o := range methodOwners {
		if !names[o] {
			t.Errorf("%s: method receiver type %s is not declared in the same shim source", key, o)
		}
	}
	return names
}

func sortedKeys(m map[string]bool) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

// TestStdlibShimDepsExact: stdlibShimDeps is CHECKED against the shim
// sources in both directions. For every shim source, the set of OTHER
// shims whose reserved names it references (the always-injected
// shimUnsupportedName aside) must equal its declared deps — a
// reference with no row is BUG-086's shape (an unclosed bundle); a row
// with no reference is a stale entry that would plant dead code.
// Every dep must also name a real shim source, and every shim source
// must have a stdlibShimDeclNames row (else its names are invisible to
// this check AND to the reserved-name collision scan).
func TestStdlibShimDepsExact(t *testing.T) {
	owner := shimNameOwner(t)
	for key := range stdlibShimSources {
		row, ok := stdlibShimDeclNames[key]
		if !ok {
			t.Errorf("%s: shim source has no stdlibShimDeclNames row", key)
			continue
		}
		rowSet := map[string]bool{}
		for _, n := range row {
			rowSet[n] = true
		}
		declared := shimSourceDecls(t, key)
		d, r := sortedKeys(declared), sortedKeys(rowSet)
		if strings.Join(d, ",") != strings.Join(r, ",") {
			t.Errorf("%s: source declares top-level names %v but stdlibShimDeclNames lists %v (the collision scan sees only the row)", key, d, r)
		}
	}
	for key, deps := range stdlibShimDeps {
		if _, ok := stdlibShimSources[key]; !ok {
			t.Errorf("stdlibShimDeps row %s names no shim source", key)
		}
		for _, dep := range deps {
			if _, ok := stdlibShimSources[dep]; !ok {
				t.Errorf("stdlibShimDeps[%s] dep %s names no shim source", key, dep)
			}
			if dep == shimUnsupportedName {
				t.Errorf("stdlibShimDeps[%s] lists %s, which rides along with every bundle and is never a declared dep", key, dep)
			}
		}
	}
	for key := range stdlibShimSources {
		want := shimSourceRefs(t, key, owner)
		delete(want, shimUnsupportedName)
		got := map[string]bool{}
		for _, dep := range stdlibShimDeps[key] {
			got[dep] = true
		}
		w, g := sortedKeys(want), sortedKeys(got)
		if strings.Join(w, ",") != strings.Join(g, ",") {
			t.Errorf("%s: source references shims %v but stdlibShimDeps declares %v", key, w, g)
		}
	}
}

// TestStdlibShimEachKeyClosedAlone: every shim source, injected with
// exactly its declared closure (plus the unsupported rider, as
// injectStdlibShims does), type-checks standing alone. Finer than the
// per-entry test: it covers shims no single table entry plants alone
// (fmtDynShimKey is only ever listed beside fmtShimBundleKey).
func TestStdlibShimEachKeyClosedAlone(t *testing.T) {
	for _, key := range sortedKeys(func() map[string]bool {
		m := map[string]bool{}
		for k := range stdlibShimSources {
			m[k] = true
		}
		return m
	}()) {
		needed := map[string]bool{key: true}
		if err := closeShimDeps(needed); err != nil {
			t.Fatalf("%s: closeShimDeps: %v", key, err)
		}
		needed[shimUnsupportedName] = true
		src := "package main\n"
		for _, name := range sortedKeys(needed) {
			src += stdlibShimSources[name]
		}
		fset := token.NewFileSet()
		f, err := parser.ParseFile(fset, "golean-stdlib-shims.go", src, parser.ParseComments)
		if err != nil {
			t.Fatalf("%s: closed bundle failed to parse: %v", key, err)
		}
		if errs := typeCheckShimFileAlone(t, fset, f); len(errs) > 0 {
			t.Errorf("%s: closed bundle %v does NOT type-check alone:\n  %s",
				key, sortedKeys(needed), strings.Join(errs, "\n  "))
		}
	}
}

// TestCloseShimDepsRefusesUnknownDep: a dependency naming no shim
// source refuses (fail closed) instead of planting an empty string.
func TestCloseShimDepsRefusesUnknownDep(t *testing.T) {
	saved := stdlibShimDeps
	defer func() { stdlibShimDeps = saved }()
	stdlibShimDeps = map[string][]string{fmtDynShimKey: {"goleanShimDoesNotExist"}}
	needed := map[string]bool{fmtDynShimKey: true}
	if err := closeShimDeps(needed); err == nil {
		t.Fatal("closeShimDeps accepted a dep with no shim source")
	}
}
