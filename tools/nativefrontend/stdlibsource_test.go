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
	"encoding/json"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
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

// TestStdlibSourceJoinLowersThroughOverlaidBuilder (slice 2): a direct
// strings.Join call reaches the REAL library function, whose Builder use
// lowers with BODIES at the three overlaid sites — no shim, no shadow
// model, no `unsafe` quarantine stub on the wire.
func TestStdlibSourceJoinLowersThroughOverlaidBuilder(t *testing.T) {
	withStdlibRoots(t)
	dir := writeMain(t, `package main

import "strings"

func subject() string { return strings.Join([]string{"a", "b"}, ",") }

func main() { subject() }
`)
	program, err := lowerProgramDir(t, dir)
	if err != nil {
		t.Fatalf("lower: %v", err)
	}
	fns := funcNames(program)
	if _, shim := fns["goleanShimStringsJoin"]; shim {
		t.Fatalf("the retired strings.Join shim was injected")
	}
	if _, real := fns["strings.Join"]; !real {
		t.Fatalf("the REAL strings.Join was not reached from a direct call; funcs: %v", keysOf(fns))
	}
	methods, _ := program["methods"].([]any)
	seen := map[string]map[string]any{}
	for _, mm := range methods {
		m, _ := mm.(map[string]any)
		seen[fmt.Sprint(m["recvType"])+"."+fmt.Sprint(m["name"])] = m
	}
	for _, want := range []string{"String", "copyCheck", "grow", "Grow", "WriteString"} {
		m, ok := seen["strings.Builder."+want]
		if !ok {
			t.Fatalf("strings.Builder.%s is not on the wire; methods: %v", want, keysOf(seen))
		}
		if reason, quarantined := m["unsupported"]; quarantined {
			t.Fatalf("strings.Builder.%s is a quarantine stub (%v) — the overlay did not apply", want, reason)
		}
	}
	// Nothing on the wire mentions the retired shadow model or an unsafe
	// refusal at an overlaid site.
	for name, m := range seen {
		if reason, quarantined := m["unsupported"]; quarantined && strings.Contains(fmt.Sprint(reason), "needs unsafe.") && strings.HasPrefix(name, "strings.Builder.") {
			t.Fatalf("overlaid site still refuses: %s: %v", name, reason)
		}
	}
}

// TestStdlibOverlayMovedBytesRefuseByName (slice 2, red-first): when the
// pinned line no longer carries the recorded bytes, the unit refuses
// naming the site — never a silent non-application (which would leave
// the H-3 unsafe stub in place) and never a substitution elsewhere.
func TestStdlibOverlayMovedBytesRefuseByName(t *testing.T) {
	withStdlibRoots(t)
	saved := stdlibOverlayTSV
	defer func() { stdlibOverlayTSV = saved }()
	stdlibOverlayTSV = strings.Replace(saved, "unsafe.String(unsafe.SliceData(b.buf), len(b.buf))\tstring(b.buf)", "unsafe.String(unsafe.SliceData(b.buf), len(b.buf)+0)\tstring(b.buf)", 1)
	if stdlibOverlayTSV == saved {
		t.Fatal("probe did not mutate the Builder.String row")
	}
	dir := writeMain(t, `package main

import "strings"

func subject() string { var b strings.Builder; b.WriteString("x"); return b.String() }

func main() { subject() }
`)
	_, err := lowerProgramDir(t, dir)
	if err == nil || !strings.Contains(err.Error(), "stdlib overlay strings/builder.go:47") || !strings.Contains(err.Error(), "NOT on that line") {
		t.Fatalf("a moved overlay site must refuse by name; got %v", err)
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
	// Slice 2: Clone is OVERLAID (stdlib-overlay.tsv row
	// internal/stringslite/strings.go:149) and lowers with a BODY — the
	// error path that BUG-089 pinned red is green.
	clone, ok := fns["internal/stringslite.Clone"]
	if !ok {
		t.Fatalf("internal/stringslite.Clone (reached through Atoi's error path) not on the wire")
	}
	if reason, q := clone["unsupported"]; q {
		t.Fatalf("Clone is still an H-3 stub (%v) — the overlay did not apply", reason)
	}
	for _, want := range []string{"strconv.Atoi", "internal/strconv.Atoi", "internal/strconv.ParseInt", "internal/strconv.ParseUint", "strconv.syntaxError"} {
		f, ok := fns[want]
		if !ok {
			t.Fatalf("%s not on the wire", want)
		}
		if _, q := f["unsupported"]; q {
			t.Fatalf("%s quarantined: %v", want, f["unsupported"])
		}
	}
	// An unsafe site the overlay does NOT cover keeps the by-name H-3
	// quarantine: slices.Insert reaches `overlaps` (unsafe.Sizeof +
	// pointer arithmetic — REFUSED, not overlaid; memo §1.3).
	dir = writeMain(t, `package main

import "slices"

func subject() int { return len(slices.Insert([]int{1, 2}, 1, 9)) }

func main() { subject() }
`)
	program, err = lowerProgramDir(t, dir)
	if err != nil {
		t.Fatalf("lower (slices.Insert): %v", err)
	}
	fns = funcNames(program)
	var overlaps map[string]any
	for name, f := range fns {
		if strings.HasPrefix(name, "slices.overlaps") {
			overlaps = f
		}
	}
	if overlaps == nil {
		t.Fatalf("slices.overlaps (reached through Insert) not on the wire; funcs: %v", keysOf(fns))
	}
	reason, _ := overlaps["unsupported"].(string)
	if !strings.Contains(reason, "unsafe.Sizeof") || !strings.Contains(reason, "slices.overlaps") {
		t.Fatalf("slices.overlaps must be an H-3 stub naming unsafe.Sizeof and the site; got %q", reason)
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
	for _, want := range []string{"count\toverlay\t5 / cap 12", "count\toverlay-import\t5 / cap 8", "count\tintercept\t0 ", "count\tprimitive\t0 / cap 2", "source-through\tstrings\t", "substitution\tinternal/bytealg/indexbyte_native.go -> indexbyte_generic.go\t", "count\tshim\t6 ", "count\tshadow-type\t5", "source-through\tbytes\t", "source-through\tslices\t", "source-through\tcmp\t", "source-through\tencoding/binary\t", "shim\tfmt.Sprintf\t", "overlay\tinternal/stringslite/strings.go:149\t`unsafe.String(&b[0], len(b))` -> `string(b)`", "overlay\tstrings/builder.go:47\t", "overlay-import\tstrings/builder.go:11\t`\"unsafe\"` -> `_ \"unsafe\"`"} {
		if !strings.Contains(out, want) {
			t.Fatalf("register dump lacks %q:\n%s", want, out)
		}
	}
	for _, retired := range []string{"shim\tstrings.Fields\t", "shim\tstrings.Split\t", "shim\tstrings.TrimSpace\t", "shim\tstrconv.FormatUint\t", "shim\tstrconv.FormatInt\t", "shim\tstrconv.ParseUint\t",
		"shim\tstrings.Join\t", "shim\tstrings.Repeat\t", "shim\terrors.New\t", "shim\tbytes.Equal\t", "shim\tslices.SortFunc\t", "shim\tencoding/binary.LittleEndian.Uint64\t", "shim\tencoding/binary.LittleEndian.PutUint64\t", "shadow-type\tstrings.Builder\t", "shadow-type\tbytes.Buffer\t", "intercept\tslices.Sort\t", "intercept\tcmp.Compare\t"} {
		if strings.Contains(out, retired) {
			t.Fatalf("register dump still lists a retired shim %q", retired)
		}
	}
	// The cap is enforced by the dump itself (red-first: overfill the
	// overlay table with cap+1 well-formed expr rows).
	saved := stdlibOverlayTSV
	over := ""
	for i := 0; i <= stdlibOverlayCap; i++ {
		over += "strings\tstrings.go\t" + itoa(i+1) + "\texpr\told" + itoa(i) + "\tnew" + itoa(i) + "\tprobe\n"
	}
	stdlibOverlayTSV = over
	_, err = stdlibRegisterDump()
	stdlibOverlayTSV = saved
	if err == nil || !strings.Contains(err.Error(), "exceed the cap") {
		t.Fatalf("an over-cap overlay table must refuse; got %v", err)
	}
	// The import-row cap (F-round): cap+1 import rows behind one expr row refuse.
	overImp := "strings\tstrings.go\t1\texpr\told\tnew\tprobe\n"
	for i := 0; i <= stdlibOverlayImportCap; i++ {
		overImp += "strings\tstrings.go\t" + itoa(i+2) + "\timport\t\"p" + itoa(i) + "\"\t_ \"p" + itoa(i) + "\"\tprobe\n"
	}
	stdlibOverlayTSV = overImp
	_, err = stdlibRegisterDump()
	stdlibOverlayTSV = saved
	if err == nil || !strings.Contains(err.Error(), "import-neutralization rows exceed the cap") {
		t.Fatalf("an over-cap import-row table must refuse; got %v", err)
	}
	// Exactly cap rows render (the cap is inclusive).
	stdlibOverlayTSV = strings.Join(strings.Split(strings.TrimRight(over, "\n"), "\n")[:stdlibOverlayCap], "\n") + "\n"
	_, err = stdlibRegisterDump()
	stdlibOverlayTSV = saved
	if err != nil {
		t.Fatalf("a table at the cap must render; got %v", err)
	}
}

// TestStdlibOverlayTableRules: the table parser's fail-closed rules
// (red-first, one probe per rule).
func TestStdlibOverlayTableRules(t *testing.T) {
	row := func(pkg, file, line, kind, old, new string) string {
		return pkg + "\t" + file + "\t" + line + "\t" + kind + "\t" + old + "\t" + new + "\treason\n"
	}
	good := row("strings", "builder.go", "47", "expr", "unsafe.String(x)", "string(x)")
	if _, err := parseStdlibOverlay(good); err != nil {
		t.Fatalf("well-formed row refused: %v", err)
	}
	for name, tsv := range map[string]string{
		"6 columns":              "strings\tbuilder.go\t47\texpr\told\tnew\n",
		"empty column":           row("strings", "builder.go", "47", "expr", "", "new"),
		"non-numeric line":       row("strings", "builder.go", "x", "expr", "old", "new"),
		"line 0":                 row("strings", "builder.go", "0", "expr", "old", "new"),
		"unallowed package":      row("fmt", "print.go", "1", "expr", "old", "new"),
		"nested file":            row("strings", "sub/x.go", "1", "expr", "old", "new"),
		"unknown kind":           row("strings", "builder.go", "1", "patch", "old", "new"),
		"substitute uses unsafe": row("strings", "builder.go", "1", "expr", "old", "unsafe.Slice(p, 1)"),
		"substitute uses abi":    row("strings", "builder.go", "1", "expr", "old", "abi.NoEscape(p)"),
		"identical old/new":      row("strings", "builder.go", "1", "expr", "same", "same"),
		"duplicate site":         good + good,
		"import not `_ `":        good + row("strings", "builder.go", "11", "import", `"unsafe"`, `"unsafe2"`),
		"import without site":    row("strings", "builder.go", "11", "import", `"unsafe"`, `_ "unsafe"`),
	} {
		if _, err := parseStdlibOverlay(tsv); err == nil {
			t.Fatalf("%s: must refuse", name)
		}
	}
	// applyStdlibOverlay: exactly-once byte check, line-local.
	rows, _ := parseStdlibOverlay(row("strings", "builder.go", "2", "expr", "unsafe.String(p)", "string(p)"))
	src := []byte("package strings\n\treturn unsafe.String(p)\nlast\n")
	out, applied, err := applyStdlibOverlay(rows, "strings", "/x/strings/builder.go", src)
	if err != nil || len(applied) != 1 || string(out) != "package strings\n\treturn string(p)\nlast\n" {
		t.Fatalf("apply: %v %v %q", err, applied, out)
	}
	if _, _, err := applyStdlibOverlay(rows, "strings", "/x/strings/builder.go", []byte("package strings\n\treturn other(p)\nlast\n")); err == nil || !strings.Contains(err.Error(), "NOT on that line") {
		t.Fatalf("moved bytes must refuse by site; got %v", err)
	}
	if _, _, err := applyStdlibOverlay(rows, "strings", "/x/strings/builder.go", []byte("package strings\n\tunsafe.String(p) + unsafe.String(p)\n")); err == nil || !strings.Contains(err.Error(), "ambiguous") {
		t.Fatalf("two occurrences must refuse; got %v", err)
	}
	if _, _, err := applyStdlibOverlay(rows, "strings", "/x/strings/builder.go", []byte("package strings\n")); err == nil || !strings.Contains(err.Error(), "only 1 line") {
		t.Fatalf("a missing line must refuse; got %v", err)
	}
	// A file the table does not name passes through byte-identical.
	same, applied, err := applyStdlibOverlay(rows, "strings", "/x/strings/other.go", src)
	if err != nil || len(applied) != 0 || string(same) != string(src) {
		t.Fatalf("untouched file changed: %v %v", err, applied)
	}
	// F2 (a): an expr row targeting an import line refuses by site.
	imp := []byte("package strings\n\nimport (\n\t\"internal/bytealg\"\n\t\"unsafe\"\n)\n\nfunc f() { _ = unsafe.Sizeof(0); _ = bytealg.MaxLen }\n")
	rows2, _ := parseStdlibOverlay(row("strings", "builder.go", "4", "expr", `"internal/bytealg"`, `zz "internal/bytealg"`))
	if _, _, err := applyStdlibOverlay(rows2, "strings", "/x/strings/builder.go", imp); err == nil || !strings.Contains(err.Error(), "inside the file's import declaration") {
		t.Fatalf("an expr row on an import line must refuse; got %v", err)
	}
	// F2 (b): after the rows apply, a LIVE banned import refuses (the
	// bytealg import is neutralized, the unsafe one is not).
	rows3, _ := parseStdlibOverlay(row("strings", "builder.go", "8", "expr", "unsafe.Sizeof(0)", "8") + row("strings", "builder.go", "4", "import", `"internal/bytealg"`, `_ "internal/bytealg"`))
	if _, _, err := applyStdlibOverlay(rows3, "strings", "/x/strings/builder.go", imp); err == nil || !strings.Contains(err.Error(), "LIVE import of \"unsafe\"") {
		t.Fatalf("a surviving live banned import must refuse; got %v", err)
	}
}

// TestStdlibOverlayCheckTypeChecks (audit fix round F3, red-first): the
// overlay check TYPE-CHECKS each overlaid package — dropping the
// builder.go:47 expr row while keeping the import rows leaves
// `unsafe.String` live behind a blank import, which byte-checking alone
// accepted (rc 0) and go/types refuses naming the file.
func TestStdlibOverlayCheckTypeChecks(t *testing.T) {
	withStdlibRoots(t)
	if _, err := stdlibOverlayCheck(); err != nil {
		t.Fatalf("the shipped table must verify: %v", err)
	}
	saved := stdlibOverlayTSV
	defer func() { stdlibOverlayTSV = saved }()
	kept := []string{}
	for _, l := range strings.Split(saved, "\n") {
		if strings.HasPrefix(l, "strings\tbuilder.go\t47\t") {
			continue
		}
		kept = append(kept, l)
	}
	stdlibOverlayTSV = strings.Join(kept, "\n")
	if stdlibOverlayTSV == saved {
		t.Fatal("probe did not drop the builder.go:47 row")
	}
	_, err := stdlibOverlayCheck()
	if err == nil || !strings.Contains(err.Error(), "does not type-check") || !strings.Contains(err.Error(), "builder.go") {
		t.Fatalf("an import row whose site still uses the package must fail the type-check naming the file; got %v", err)
	}
}

// TestStdlibOverlayRowMustApply (audit fix round F6): a row naming a file
// the package does not select refuses at load, not silently no-ops.
func TestStdlibOverlayRowMustApply(t *testing.T) {
	withStdlibRoots(t)
	saved := stdlibOverlayTSV
	defer func() { stdlibOverlayTSV = saved }()
	stdlibOverlayTSV = saved + "strings\tnosuchfile.go\t1\texpr\tunsafe.String(x)\tstring(x)\tprobe\n"
	dir := writeMain(t, `package main

import "strings"

func subject() string { return strings.Repeat("x", 2) }

func main() { subject() }
`)
	_, err := lowerProgramDir(t, dir)
	if err == nil || !strings.Contains(err.Error(), "strings/nosuchfile.go:1") || !strings.Contains(err.Error(), "applied 0 time(s)") {
		t.Fatalf("a row that never applies must refuse by site; got %v", err)
	}
}

// TestSlicesSortIsTheRealGenericEverywhere (memo §3 row M, lane fr4-rowm,
// 2026-09-04): the `slices.Sort` intercept onto the `sortSlice` machine op
// is RETIRED, so every shape — the direct call, `defer`, `go` — reaches the
// real source-through generic: the `slices.Sort[…]` stencil and its
// `pdqsortOrdered` closure are on the wire, the subject is NOT quarantined,
// and NO `sort-slice` node is emitted (the op is unreferenced). Before row
// M the defer/go shapes refused by name (audit fix round F1) and the
// direct call was the machine op at integer kinds only; the intercept
// table is empty now, and the predicate says so for slices.Sort.
func TestSlicesSortIsTheRealGenericEverywhere(t *testing.T) {
	withStdlibRoots(t)
	if len(frontendInterceptedLibraryMembers) != 0 {
		t.Fatalf("the intercept table must be EMPTY since row M (a new entry is a register widening): %v", frontendInterceptedLibraryMembers)
	}
	for _, shape := range []string{"", "defer", "go"} {
		dir := writeMain(t, `package main

import "slices"

func subject() int { s := []string{"c", "a", "b"}; `+shape+` slices.Sort(s); return len(s) }

func main() { subject() }
`)
		program, err := lowerProgramDir(t, dir)
		if err != nil {
			t.Fatalf("%q: lower: %v", shape, err)
		}
		fns := funcNames(program)
		subj, ok := fns["subject"]
		if !ok {
			t.Fatalf("%q: subject not on the wire", shape)
		}
		if reason, stubbed := subj["unsupported"]; stubbed {
			t.Fatalf("%q: subject quarantined — slices.Sort must lower through the real generic; got %v", shape, reason)
		}
		if _, real := fns["slices.Sort[[]string,string]"]; !real {
			t.Fatalf("%q: the real slices.Sort stencil is not on the wire; funcs: %v", shape, keysOf(fns))
		}
		if _, pdq := fns["slices.pdqsortOrdered[string]"]; !pdq {
			t.Fatalf("%q: pdqsortOrdered[string] not stenciled; funcs: %v", shape, keysOf(fns))
		}
		if strings.Contains(mustJSON(t, program), `"sort-slice"`) {
			t.Fatalf("%q: a sort-slice machine-op node was emitted — the intercept is retired", shape)
		}
	}
}

func mustJSON(t *testing.T, v any) string {
	t.Helper()
	b, err := json.Marshal(v)
	if err != nil {
		t.Fatal(err)
	}
	return string(b)
}

func keysOf(m map[string]map[string]any) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	return out
}

// ---- audit fix round (2026-09-03): B2, F3, F4, F5, F7 ----

// B2: a program calling errors.Is/As/Unwrap (whose bodies dispatch on
// UNNAMED interface types: `err.(interface{ Unwrap() error })`) must
// EXPORT — the interface method's *types.Func has no declaration site and
// must not be mistaken for a package-level function (the regression the
// audit found: the whole export died "no declaration site").
func TestStdlibSourceErrorsWrapExports(t *testing.T) {
	withStdlibRoots(t)
	dir := writeMain(t, `package main

import (
	"errors"
	"strconv"
)

type wrapped struct{ inner error }

func (w wrapped) Error() string { return "w:" + w.inner.Error() }
func (w wrapped) Unwrap() error { return w.inner }

func subject() (bool, bool, bool) {
	err := &strconv.NumError{Func: "ParseUint", Num: "x", Err: strconv.ErrSyntax}
	w := wrapped{err}
	var ne *strconv.NumError
	return errors.Is(w, strconv.ErrSyntax), errors.As(w, &ne), errors.Unwrap(w) == err
}

func main() { subject() }
`)
	program, err := lowerProgramDir(t, dir)
	if err != nil {
		t.Fatalf("a program calling errors.Is/As/Unwrap must export (per-decl quarantine at most): %v", err)
	}
	fns := funcNames(program)
	for _, want := range []string{"errors.Is", "errors.As", "errors.Unwrap", "errors.is", "errors.as"} {
		if _, ok := fns[want]; !ok {
			t.Fatalf("%s not on the wire (bodied or stubbed); have %d funcs", want, len(fns))
		}
	}
}

// F3: the pin is BIDIRECTIONAL — a pinned file that is not selected for
// its package refuses (a deleted/renamed upstream file must not silently
// change the lowered package).
func TestStdlibPinnedFileNotSelectedRefuses(t *testing.T) {
	withStdlibRoots(t)
	files, err := selectLibraryFiles("strings")
	if err != nil {
		t.Fatal(err)
	}
	pin, err := loadStdlibPin()
	if err != nil {
		t.Fatal(err)
	}
	if err := checkPinnedFilesSelected("strings", files, pin); err != nil {
		t.Fatalf("the tracked pin's strings rows must all be selected: %v", err)
	}
	// Drop strings/reader.go from the selection (the audit's probe:
	// deleting the unreached, import-bearing file left exit 0).
	kept := []string{}
	for _, f := range files {
		if !strings.HasSuffix(f, "/strings/reader.go") {
			kept = append(kept, f)
		}
	}
	if len(kept) == len(files) {
		t.Fatalf("probe setup: strings/reader.go not among the selected files")
	}
	err = checkPinnedFilesSelected("strings", kept, pin)
	if err == nil || !strings.Contains(err.Error(), "strings/reader.go") || !strings.Contains(err.Error(), "NOT among the files selected") {
		t.Fatalf("a pinned-but-unselected file must refuse naming it; got %v", err)
	}
	// A row of ANOTHER package (or a sub-package) is not this package's.
	if err := checkPinnedFilesSelected("unicode", mustSelect(t, "unicode"), pin); err != nil {
		t.Fatalf("unicode must not be charged with unicode/utf8's rows: %v", err)
	}
}

func mustSelect(t *testing.T, path string) []string {
	t.Helper()
	files, err := selectLibraryFiles(path)
	if err != nil {
		t.Fatal(err)
	}
	return files
}

// F4: the host toolchain must be the pinned one.
func TestStdlibHostToolchainPinned(t *testing.T) {
	if err := checkHostToolchainPinned("go1.26.5", "go1.26.5"); err != nil {
		t.Fatal(err)
	}
	err := checkHostToolchainPinned("go1.26.6", "go1.26.5")
	if err == nil || !strings.Contains(err.Error(), `"go1.26.6"`) || !strings.Contains(err.Error(), `"go1.26.5"`) {
		t.Fatalf("a host toolchain off the pin must refuse naming both; got %v", err)
	}
}

// F5: a library unit's quarantine reason names its declaration.
func TestStdlibQuarantineReasonNamesSite(t *testing.T) {
	withStdlibRoots(t)
	dir := writeMain(t, `package main

import "strconv"

func subject() string { return strconv.FormatFloat(1.5, 'g', -1, 64) }

func main() { subject() }
`)
	program, err := lowerProgramDir(t, dir)
	if err != nil {
		t.Fatalf("lower: %v", err)
	}
	fns := funcNames(program)
	found := false
	for name, f := range fns {
		reason, quarantined := f["unsupported"].(string)
		if !quarantined || !strings.HasPrefix(name, "internal/strconv.") {
			continue
		}
		found = true
		if !strings.HasPrefix(reason, name+": ") && !strings.HasPrefix(reason, "stdlib source-through: "+name) {
			t.Fatalf("library quarantine reason for %s does not name its site: %q", name, reason)
		}
	}
	if !found {
		t.Fatalf("expected at least one quarantined internal/strconv declaration on the float path")
	}
}

// F7: a body that is solely panic("unimplemented") is recognized (and
// quarantined by emitFuncDecl for library units), and only that shape.
func TestUnimplementedPanicBodyShape(t *testing.T) {
	parse := func(src string) *ast.FuncDecl {
		f, err := parser.ParseFile(token.NewFileSet(), "x.go", "package p\n"+src, 0)
		if err != nil {
			t.Fatal(err)
		}
		return f.Decls[0].(*ast.FuncDecl)
	}
	if !isUnimplementedPanicBody(parse(`func Index(a, b []byte) int { panic("unimplemented") }`).Body) {
		t.Fatalf("index_generic.go's placeholder shape must be recognized")
	}
	for _, src := range []string{
		`func f() int { panic("boom") }`,
		`func f() int { x := 1; panic("unimplemented") }`,
		`func f() int { return 0 }`,
		`func f() { panic(msg) }`,
	} {
		if isUnimplementedPanicBody(parse(src).Body) {
			t.Fatalf("misrecognized as an unimplemented placeholder: %s", src)
		}
	}
}

// F7 end-to-end: reaching a placeholder body through the library must
// land as a NAMED quarantine stub, never as a modeled panic. The only way
// to reach one at the pin is a direct user call into internal/bytealg —
// which the import rules forbid for user code — so the check runs the
// emitter's own arm over the real declaration via a library unit that
// declares it: internal/bytealg is loaded when strings is.
func TestUnimplementedPlaceholderQuarantinesByName(t *testing.T) {
	withStdlibRoots(t)
	units, idx, err := loadLibraryUnitForTest(t, "internal/bytealg")
	if err != nil {
		t.Fatal(err)
	}
	e := &emitter{fset: idx.fset, info: units.info, pkg: units.pkg}
	e.setUnits([]*sourcePkg{units})
	e.setUnit(units)
	var cutover *ast.FuncDecl
	for _, f := range units.files {
		for _, d := range f.Decls {
			if fd, ok := d.(*ast.FuncDecl); ok && fd.Name.Name == "Cutover" {
				cutover = fd
			}
		}
	}
	if cutover == nil {
		t.Fatalf("index_generic.go's Cutover not in the selected files")
	}
	_, err = e.emitFuncDecl(cutover)
	if err == nil || !strings.Contains(err.Error(), "internal/bytealg.Cutover") || !strings.Contains(err.Error(), `panic("unimplemented")`) {
		t.Fatalf("a placeholder body must refuse by name; got %v", err)
	}
}

type libTestIdx struct{ fset *token.FileSet }

// loadLibraryUnitForTest parses + type-checks one allowed library package
// standing alone (its imports from export data), for emitter-arm tests.
func loadLibraryUnitForTest(t *testing.T, path string) (*sourcePkg, libTestIdx, error) {
	t.Helper()
	fset := token.NewFileSet()
	l := newLoader(fset, t.TempDir())
	pin, err := loadStdlibPin()
	if err != nil {
		return nil, libTestIdx{}, err
	}
	unit, err := l.parseLibrary(path, pin)
	if err != nil {
		return nil, libTestIdx{}, err
	}
	lang, err := pinnedLangVersion()
	if err != nil {
		return nil, libTestIdx{}, err
	}
	unit.info = newTypesInfo()
	conf := types.Config{Importer: l.stdlib, GoVersion: lang}
	pkg, err := conf.Check(unit.path, fset, unit.files, unit.info)
	if err != nil {
		return nil, libTestIdx{}, err
	}
	unit.pkg = pkg
	return unit, libTestIdx{fset: fset}, nil
}
