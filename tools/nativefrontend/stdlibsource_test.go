package main

// Unit tests for the stdlib source-through loader (stdlibsource.go /
// stdlibreach.go), slice 1 (2026-09-03). Two families:
//
//   1. FAIL-CLOSED GUARDS, red-first: the library pin (a mutated hash
//      refuses by path; a missing row refuses), the rev check (a VERSION
//      off the pin refuses), the substitution table (a DROP not selected
//      or an ADD that does not exist refuses; a malformed row refuses),
//      and the register caps.
//   2. THE LOWERING SHAPE over the real pinned GOROOT (deps/go/src via
//      ../../): a program calling strings.Fields lowers the REAL
//      `strings.Fields` (no injected shim), reachability keeps only the
//      declarations the program can execute, a retained shim's direct
//      call does NOT reach its real declaration, and a reached body that
//      needs `unsafe` (internal/stringslite.Clone) lands as an H-3 stub
//      whose reason names the site.
//
// These tests need deps/go at the pin (scripts/setup-deps --only go) and
// SKIP loudly — never pass vacuously — when it is absent: a repo without
// the checkout cannot certify anything here, and scripts/ci's own gates
// (check-frontend-pins, check-spec-anchors) already fail closed on that.

import (
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// withStdlibRoots points the loader at the repo's deps/go/src and pin for
// the duration of a test (tests run with cwd = tools/nativefrontend).
func withStdlibRoots(t *testing.T) {
	t.Helper()
	savedRoot, savedPin := stdlibSrcRoot, stdlibPinPath
	stdlibSrcRoot = filepath.Join("..", "..", "deps", "go", "src")
	stdlibPinPath = filepath.Join("..", "..", "baselines", "stdlib-pin.tsv")
	t.Cleanup(func() { stdlibSrcRoot, stdlibPinPath = savedRoot, savedPin })
	if err := checkStdlibSrcRev(); err != nil {
		t.Skipf("pinned GOROOT source not available (%v) — run scripts/setup-deps --only go; this test cannot certify without it", err)
	}
}

// lowerProgramDir runs the REAL pipeline (parse → shims → loadProgram →
// emitProgram) over a directory holding a main package.
func lowerProgramDir(t *testing.T, dir string) (map[string]any, error) {
	t.Helper()
	fset := token.NewFileSet()
	pkgs, err := parser.ParseDir(fset, dir, nonTestGoFile, parser.ParseComments)
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	var files []*ast.File
	for _, pkg := range pkgs {
		for _, f := range pkg.Files {
			files = append(files, f)
		}
	}
	if shimFile, err := injectStdlibShims(fset, files); err != nil {
		return nil, err
	} else if shimFile != nil {
		files = append(files, shimFile)
	}
	units, err := loadProgram(fset, dir, files)
	if err != nil {
		return nil, err
	}
	mainUnit := units[len(units)-1]
	em := &emitter{fset: fset, info: mainUnit.info, pkg: mainUnit.pkg}
	em.setUnits(units)
	return em.emitProgram(files)
}

func writeMain(t *testing.T, src string) string {
	t.Helper()
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "main.go"), []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	return dir
}

func funcNames(program map[string]any) map[string]map[string]any {
	out := map[string]map[string]any{}
	fs, _ := program["funcs"].([]any)
	for _, f := range fs {
		if m, ok := f.(map[string]any); ok {
			if n, _ := m["name"].(string); n != "" {
				out[n] = m
			}
		}
	}
	return out
}

func TestStdlibSourceFieldsLowersRealBodyPruned(t *testing.T) {
	withStdlibRoots(t)
	dir := writeMain(t, `package main

import "strings"

func subject() int { return len(strings.Fields(" a  b\u00a0c ")) }

func main() { subject() }
`)
	program, err := lowerProgramDir(t, dir)
	if err != nil {
		t.Fatalf("lower: %v", err)
	}
	fns := funcNames(program)
	for _, want := range []string{"strings.Fields", "strings.FieldsFunc", "unicode.IsSpace", "unicode.isExcludingLatin"} {
		f, ok := fns[want]
		if !ok {
			t.Fatalf("real library function %s not on the wire; have %v", want, keysOf(fns))
		}
		if _, quarantined := f["unsupported"]; quarantined {
			t.Fatalf("%s is quarantined: %v", want, f["unsupported"])
		}
	}
	if _, shim := fns["goleanShimStringsFields"]; shim {
		t.Fatalf("retired shim goleanShimStringsFields is still injected")
	}
	// Reachability: strings has ~100 exported functions; only Fields'
	// closure is on the wire. unicode.IsUpper, strings.Split are not.
	for _, absent := range []string{"strings.Split", "strings.genSplit", "unicode.IsUpper", "unicode.IsLetter", "strings.Index"} {
		if _, present := fns[absent]; present {
			t.Fatalf("unreached library function %s was emitted (pruning failed)", absent)
		}
	}
	// The pruned globals: White_Space and asciiSpace, not unicode's
	// Categories/Scripts maps.
	globals, _ := program["globals"].([]any)
	seen := map[string]bool{}
	for _, g := range globals {
		if m, ok := g.(map[string]any); ok {
			seen[m["name"].(string)] = true
		}
	}
	for _, want := range []string{"unicode.White_Space", "unicode._White_Space", "strings.asciiSpace"} {
		if !seen[want] {
			t.Fatalf("reached library global %s missing; have %v", want, seen)
		}
	}
	for _, absent := range []string{"unicode.Categories", "unicode.Scripts", "unicode.Letter", "unicode.properties"} {
		if seen[absent] {
			t.Fatalf("unreached library global %s was emitted (pruning failed)", absent)
		}
	}
}

func TestStdlibSourceRetainedShimCallDoesNotReachRealDecl(t *testing.T) {
	withStdlibRoots(t)
	dir := writeMain(t, `package main

import "strconv"

func subject() (uint64, error) { return strconv.ParseUint("7", 10, 64) }

func main() { subject() }
`)
	program, err := lowerProgramDir(t, dir)
	if err != nil {
		t.Fatalf("lower: %v", err)
	}
	fns := funcNames(program)
	if _, shim := fns["goleanShimStrconvParseUint"]; !shim {
		t.Fatalf("retained shim goleanShimStrconvParseUint not injected for a direct ParseUint call")
	}
	if _, real := fns["strconv.ParseUint"]; real {
		t.Fatalf("the REAL strconv.ParseUint was reached from a shimmed direct call (its error path would drag Quote's tables onto the wire for nothing)")
	}
}

func TestStdlibSourceUnsafeSiteQuarantinesByName(t *testing.T) {
	withStdlibRoots(t)
	dir := writeMain(t, `package main

import "strconv"

func subject() int {
	n, err := strconv.Atoi("42")
	if err != nil {
		return -1
	}
	return n
}

func main() { subject() }
`)
	program, err := lowerProgramDir(t, dir)
	if err != nil {
		t.Fatalf("lower: %v", err)
	}
	fns := funcNames(program)
	clone, ok := fns["internal/stringslite.Clone"]
	if !ok {
		t.Fatalf("internal/stringslite.Clone (reached through Atoi's error path) not on the wire")
	}
	reason, _ := clone["unsupported"].(string)
	if !strings.Contains(reason, "unsafe.String") || !strings.Contains(reason, "internal/stringslite.Clone") {
		t.Fatalf("Clone must be an H-3 stub naming unsafe.String and the site; got %q", reason)
	}
	// The happy path (real Atoi → internal/strconv.Atoi) is bodied.
	for _, want := range []string{"strconv.Atoi", "internal/strconv.Atoi", "internal/strconv.ParseInt", "internal/strconv.ParseUint"} {
		f, ok := fns[want]
		if !ok {
			t.Fatalf("%s not on the wire", want)
		}
		if _, q := f["unsupported"]; q {
			t.Fatalf("%s quarantined: %v", want, f["unsupported"])
		}
	}
}

func TestStdlibSourceNoLibraryImportIsByteIdenticalPath(t *testing.T) {
	// A program importing no allowed library must not touch the library
	// root at all (old single-unit path): point the root at a bogus dir
	// and lower a plain program.
	saved := stdlibSrcRoot
	stdlibSrcRoot = filepath.Join(t.TempDir(), "nowhere")
	t.Cleanup(func() { stdlibSrcRoot = saved })
	dir := writeMain(t, "package main\n\nfunc subject() int { return 1 }\n\nfunc main() { subject() }\n")
	if _, err := lowerProgramDir(t, dir); err != nil {
		t.Fatalf("a library-free program must not consult the library root: %v", err)
	}
}

// ---- fail-closed guards, red-first ----

func TestStdlibPinMismatchRefusesByPath(t *testing.T) {
	withStdlibRoots(t)
	files, err := selectLibraryFiles("unicode/utf8")
	if err != nil {
		t.Fatal(err)
	}
	pin, err := loadStdlibPin()
	if err != nil {
		t.Fatal(err)
	}
	if err := checkLibraryFilesPinned("unicode/utf8", files, pin); err != nil {
		t.Fatalf("the tracked pin must match the pinned checkout: %v", err)
	}
	// Mutate one byte of the recorded hash: must refuse naming the file.
	bad := map[string]string{}
	for k, v := range pin {
		bad[k] = v
	}
	key := "unicode/utf8/utf8.go"
	h := []byte(bad[key])
	if h[0] == '0' {
		h[0] = '1'
	} else {
		h[0] = '0'
	}
	bad[key] = string(h)
	err = checkLibraryFilesPinned("unicode/utf8", files, bad)
	if err == nil || !strings.Contains(err.Error(), key) || !strings.Contains(err.Error(), "DIFFERS") {
		t.Fatalf("a mutated pin hash must refuse naming %s; got %v", key, err)
	}
	// A missing row refuses too.
	delete(bad, key)
	err = checkLibraryFilesPinned("unicode/utf8", files, bad)
	if err == nil || !strings.Contains(err.Error(), "NO row") {
		t.Fatalf("a missing pin row must refuse; got %v", err)
	}
}

func TestStdlibSrcRevDriftRefuses(t *testing.T) {
	saved := stdlibSrcRoot
	root := t.TempDir()
	if err := os.MkdirAll(filepath.Join(root, "src"), 0o755); err != nil {
		t.Fatal(err)
	}
	stdlibSrcRoot = filepath.Join(root, "src")
	t.Cleanup(func() { stdlibSrcRoot = saved })
	if err := checkStdlibSrcRev(); err == nil || !strings.Contains(err.Error(), "cannot read") {
		t.Fatalf("a root without VERSION must refuse; got %v", err)
	}
	if err := os.WriteFile(filepath.Join(root, "VERSION"), []byte("go1.25.0\ntime 2025-01-01T00:00:00Z\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	err := checkStdlibSrcRev()
	if err == nil || !strings.Contains(err.Error(), `"go1.25.0"`) || !strings.Contains(err.Error(), "go1.26.5") {
		t.Fatalf("a VERSION off the pin must refuse naming both; got %v", err)
	}
}

func TestStdlibSubstitutionTableFailsClosed(t *testing.T) {
	if _, err := parseStdlibSubstitutions("internal/bytealg\tonly-three\tcols\n"); err == nil {
		t.Fatalf("a malformed substitution row must refuse")
	}
	rows, err := parseStdlibSubstitutions(stdlibSubstitutionsTSV)
	if err != nil {
		t.Fatalf("embedded table: %v", err)
	}
	if len(rows) == 0 {
		t.Fatalf("embedded table has no rows")
	}
	// A synthetic package dir where the DROP file is not selected (does
	// not exist) — the table must refuse rather than lower a body-less
	// declaration.
	saved := stdlibSrcRoot
	root := t.TempDir()
	stdlibSrcRoot = filepath.Join(root, "src")
	t.Cleanup(func() { stdlibSrcRoot = saved })
	dir := filepath.Join(stdlibSrcRoot, "internal", "bytealg")
	if err := os.MkdirAll(dir, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "bytealg.go"), []byte("package bytealg\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	_, err = selectLibraryFiles("internal/bytealg")
	if err == nil || !strings.Contains(err.Error(), "listed as a DROP but go/build did not select it") {
		t.Fatalf("a DROP row for an unselected file must refuse; got %v", err)
	}
	// Now the drops exist but an ADD does not.
	for _, d := range []string{"indexbyte_native.go", "index_native.go", "index_amd64.go", "count_native.go", "compare_native.go"} {
		if err := os.WriteFile(filepath.Join(dir, d), []byte("package bytealg\n"), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	_, err = selectLibraryFiles("internal/bytealg")
	if err == nil || !strings.Contains(err.Error(), "listed as an ADD but does not exist") {
		t.Fatalf("an ADD row for a missing file must refuse; got %v", err)
	}
}

func TestStdlibRegisterDumpCaps(t *testing.T) {
	out, err := stdlibRegisterDump()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"count\toverlay\t0 / cap 12", "count\tprimitive\t0 / cap 2", "source-through\tstrings\t", "substitution\tinternal/bytealg/indexbyte_native.go -> indexbyte_generic.go\t", "shim\tstrconv.ParseUint\t"} {
		if !strings.Contains(out, want) {
			t.Fatalf("register dump lacks %q:\n%s", want, out)
		}
	}
	for _, retired := range []string{"shim\tstrings.Fields\t", "shim\tstrings.Split\t", "shim\tstrings.TrimSpace\t", "shim\tstrconv.FormatUint\t", "shim\tstrconv.FormatInt\t"} {
		if strings.Contains(out, retired) {
			t.Fatalf("register dump still lists a retired shim %q", retired)
		}
	}
	// The cap is enforced by the dump itself (red-first: overfill it).
	saved := stdlibOverlays
	stdlibOverlays = map[string]string{}
	for i := 0; i <= stdlibOverlayCap; i++ {
		stdlibOverlays["x."+itoa(i)] = "probe"
	}
	_, err = stdlibRegisterDump()
	stdlibOverlays = saved
	if err == nil || !strings.Contains(err.Error(), "exceed the cap") {
		t.Fatalf("an over-cap overlay table must refuse; got %v", err)
	}
}

func keysOf(m map[string]map[string]any) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	return out
}
