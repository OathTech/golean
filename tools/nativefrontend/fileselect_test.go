package main

// Unit tests for the go/build-pinned file selection (BUG-108,
// fileselect.go). The corpus rows source-selection/* pin the OBSERVABLE
// contract through the real runner (an excluded init must not run; an
// included suffix must); these pin what the differential structurally
// cannot see: the refusal texts, the selected-set contract on every
// filename shape go/build knows, and the one shape the oracle harness
// generator cannot row (an excluded file with invalid syntax — it parses
// every *.go before `go run` sees the package).

import (
	"go/ast"
	"go/token"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"testing"
)

const selMain = "package main\n\nvar x = 1\n\nfunc probe() int { return x }\n\nfunc main() { println(probe()) }\n"
const selInit = "package main\n\nfunc init() { x = 2 }\n"

func writeDir(t *testing.T, files map[string]string) string {
	t.Helper()
	dir := t.TempDir()
	for name, src := range files {
		if err := os.MkdirAll(filepath.Dir(filepath.Join(dir, name)), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(dir, name), []byte(src), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	return dir
}

func baseNames(fset *token.FileSet, files []*ast.File) []string {
	out := make([]string, 0, len(files))
	for _, f := range files {
		out = append(out, filepath.Base(fset.Position(f.Package).Filename))
	}
	sort.Strings(out)
	return out
}

func TestSelectPackageFilesFilenameRules(t *testing.T) {
	// Every filename shape go/build's goodOSArchFile/matchFile decides,
	// under the pinned linux/amd64 target. `included` = gc compiles it.
	cases := []struct {
		name     string
		included bool
	}{
		{"extra_windows.go", false},
		{"extra_arm64.go", false},
		{"extra_linux_arm64.go", false}, // OS half matches, arch half does not
		{"extra_windows_amd64.go", false},
		{"_ignored.go", false},
		{".hidden.go", false},
		{"extra_test.go", false}, // a test file is never part of the program
		{"x_linux.go", true},
		{"x_amd64.go", true},
		{"x_linux_amd64.go", true},
		{"linux.go", true},   // no underscore prefix: not a tag (Go 1.4 rule)
		{"windows.go", true}, // likewise — gc compiles windows.go on linux
		{"plain.go", true},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			src := selInit
			if strings.HasSuffix(c.name, "_test.go") {
				src = "package main\n"
			}
			dir := writeDir(t, map[string]string{"main.go": selMain, c.name: src})
			fset := token.NewFileSet()
			files, err := selectPackageFiles(fset, dir)
			if err != nil {
				t.Fatalf("selectPackageFiles: %v", err)
			}
			want := []string{"main.go"}
			if c.included {
				want = append(want, c.name)
				sort.Strings(want)
			}
			if got := baseNames(fset, files); strings.Join(got, ",") != strings.Join(want, ",") {
				t.Fatalf("selected %v, want %v", got, want)
			}
		})
	}
}

func TestSelectPackageFilesExcludedFilesAreNeverRead(t *testing.T) {
	// The shape the oracle harness generator cannot row: excluded files
	// with content gc never reads — invalid syntax, a redeclaration, an
	// unadmitted import, a second package clause. Selection must succeed
	// with exactly main.go, and the excluded files' contents must not
	// influence the outcome (they are never parsed).
	dir := writeDir(t, map[string]string{
		"main.go":            selMain,
		"_scratch.go":        "this is not Go at all\n",
		".editor-swap.go":    "package main\nfunc (\n",
		"extra_windows.go":   "package main\n\nvar x = 99\n\nfunc probe() int { return -1 }\n",
		"extra_arm64.go":     "package other\n",
		"_imports.go":        "package main\n\nimport \"os\"\n\nfunc init() { x = len(os.Args) }\n",
		"garbage_windows.go": "\x00\x01 not even text",
	})
	fset := token.NewFileSet()
	files, err := selectPackageFiles(fset, dir)
	if err != nil {
		t.Fatalf("selectPackageFiles: %v", err)
	}
	if got := baseNames(fset, files); strings.Join(got, ",") != "main.go" {
		t.Fatalf("selected %v, want [main.go]", got)
	}
}

func TestSelectPackageFilesRefusalsByName(t *testing.T) {
	cases := []struct {
		label string
		files map[string]string
		want  []string // substrings of the refusal
	}{
		{"invalid header in a SELECTED file (gc's error, not ours to skip)",
			map[string]string{"main.go": selMain, "bad.go": "package main\n\nimport (\n"},
			[]string{"file selection", "bad.go"}},
		{"cgo file",
			map[string]string{"main.go": selMain, "c.go": "package main\n\nimport \"C\"\n"},
			[]string{"c.go", "import \"C\"", "cgo is outside the modeled fragment"}},
		{"assembly source gc would assemble",
			map[string]string{"main.go": selMain, "asm_amd64.s": "TEXT ·f(SB),0,$0\n\tRET\n"},
			[]string{"asm_amd64.s", "non-Go sources"}},
		{"two package clauses among the selected files",
			map[string]string{"main.go": selMain, "other.go": "package other\n"},
			[]string{"file selection", "found packages"}},
		{"no Go file selected (only excluded ones)",
			map[string]string{"_only.go": selMain},
			[]string{"file selection", "no buildable Go source files"}},
		{"excluded file carrying a reserved-tag constraint (standing policy: refuse, never silently include or drop)",
			map[string]string{"main.go": selMain, "x_windows.go": "//go:build cgo\n\npackage main\n"},
			[]string{"x_windows.go", "reserved tag", "cgo"}},
		{"excluded file carrying an excluding custom constraint (standing policy)",
			map[string]string{"main.go": selMain, "x_windows.go": "//go:build ignore\n\npackage main\n"},
			[]string{"x_windows.go", "EXCLUDED by build constraint"}},
		{"selected file carrying a reserved-tag constraint (standing policy, unchanged)",
			map[string]string{"main.go": selMain, "x.go": "//go:build linux\n\npackage main\n"},
			[]string{"x.go", "reserved tag", "linux"}},
	}
	for _, c := range cases {
		t.Run(c.label, func(t *testing.T) {
			dir := writeDir(t, c.files)
			_, err := selectPackageFiles(token.NewFileSet(), dir)
			if err == nil {
				t.Fatalf("expected a refusal")
			}
			for _, w := range c.want {
				if !strings.Contains(err.Error(), w) {
					t.Fatalf("refusal %q does not name %q", err.Error(), w)
				}
			}
		})
	}
}

func TestSelectPackageFilesConstraintPolicyAcceptances(t *testing.T) {
	// The one narrow acceptance of langversion.go survives: a custom-tag
	// constraint true with every tag unset is inert (raftsubject's
	// `//go:build !with_tla`). And a `_`/`.`-prefixed file is dropped
	// whatever its header says — gc never opens it.
	dir := writeDir(t, map[string]string{
		"main.go":    selMain,
		"nop.go":     "//go:build !with_tla\n\npackage main\n\nvar nop = 0\n",
		"_tagged.go": "//go:build cgo\n\npackage main\n",
	})
	fset := token.NewFileSet()
	files, err := selectPackageFiles(fset, dir)
	if err != nil {
		t.Fatalf("selectPackageFiles: %v", err)
	}
	if got := baseNames(fset, files); strings.Join(got, ",") != "main.go,nop.go" {
		t.Fatalf("selected %v, want [main.go nop.go]", got)
	}
}

// lowerDir runs the real pipeline (selection → shims → loadProgram →
// emitProgram) over a directory holding a main package.
func lowerDir(t *testing.T, dir string) (map[string]any, error) {
	t.Helper()
	fset := token.NewFileSet()
	files, err := selectPackageFiles(fset, dir)
	if err != nil {
		return nil, err
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

func fileOrderOf(t *testing.T, program map[string]any) map[string][]string {
	t.Helper()
	out := map[string][]string{}
	fo, _ := program["fileOrder"].([]any)
	for _, u := range fo {
		m := u.(map[string]any)
		var names []string
		for _, n := range m["files"].([]any) {
			names = append(names, n.(string))
		}
		out[m["package"].(string)] = names
	}
	return out
}

func TestWireRecordsSelectionAndTarget(t *testing.T) {
	// The wire's fileOrder lists exactly the SELECTED files of every unit
	// (main and a case-local import), and buildContext records the pinned
	// target the decoder checks against its own pin.
	dir := writeDir(t, map[string]string{
		"main.go":          "package main\n\nimport \"lib\"\n\nfunc probe() int { return lib.V }\n\nfunc main() { println(probe()) }\n",
		"extra_windows.go": "package main\n\nfunc init() { panic(\"never\") }\n",
		"lib/lib.go":       "package lib\n\nvar V = 1\n",
		"lib/_extra.go":    "package lib\n\nfunc init() { V = 2 }\n",
		"lib/lib_arm64.go": "package lib\n\nfunc init() { V = 3 }\n",
	})
	program, err := lowerDir(t, dir)
	if err != nil {
		t.Fatalf("lower: %v", err)
	}
	fo := fileOrderOf(t, program)
	if got := strings.Join(fo["main"], ","); got != "main.go" {
		t.Fatalf("main fileOrder %q, want main.go", got)
	}
	if got := strings.Join(fo["lib"], ","); got != "lib.go" {
		t.Fatalf("lib fileOrder %q, want lib.go", got)
	}
	bc, ok := program["buildContext"].(map[string]any)
	if !ok {
		t.Fatalf("wire has no buildContext record")
	}
	want := map[string]any{"goos": "linux", "goarch": "amd64", "compiler": "gc", "cgoEnabled": true}
	for k, v := range want {
		if bc[k] != v {
			t.Fatalf("buildContext[%s] = %v, want %v", k, bc[k], v)
		}
	}
	if tags, ok := bc["buildTags"].([]any); !ok || len(tags) != 0 {
		t.Fatalf("buildContext.buildTags = %v, want []", bc["buildTags"])
	}
	if len(bc) != 5 {
		t.Fatalf("buildContext has %d keys, want 5 (goos goarch compiler cgoEnabled buildTags)", len(bc))
	}
}

func TestExcludedRedeclarationLowers(t *testing.T) {
	// source-selection/excluded-conflict in unit form: the excluded file
	// redeclares names; the package type-checks and lowers because the
	// file is never read.
	dir := writeDir(t, map[string]string{
		"main.go":          "package main\n\nvar conflict = 1\n\nfunc helper() int { return conflict }\n\nfunc probe() int { return helper() }\n\nfunc main() { println(probe()) }\n",
		"extra_windows.go": "package main\n\nvar conflict = 99\n\nfunc helper() int { return -1 }\n",
	})
	program, err := lowerDir(t, dir)
	if err != nil {
		t.Fatalf("lower: %v", err)
	}
	if _, ok := funcNames(program)["probe"]; !ok {
		t.Fatalf("probe not emitted")
	}
}
