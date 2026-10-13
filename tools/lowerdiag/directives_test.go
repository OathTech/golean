package main

import (
	"os"
	"path/filepath"
	"testing"
)

// The static judge's directive scan matches the frontend's
// (tools/nativefrontend/directives.go; BUG-127, BUG-128): a //go: verb
// outside the allowlist or a line directive is one certain, export-scoped
// compiler-directive finding; a //go:debug line is a runtime-setting
// finding; the allowed verbs and prose shapes are none. The dynamic pass
// classifies the frontend's refusal texts to the same causes.
func TestCompilerDirectiveParity(t *testing.T) {
	if err := initCauses(); err != nil {
		t.Fatal(err)
	}
	sup, err := newSupply("../../docs/stdlib-admission-register.md")
	if err != nil {
		t.Fatal(err)
	}
	count := func(t *testing.T, src string) map[string]int {
		t.Helper()
		dir := t.TempDir()
		if err := os.WriteFile(filepath.Join(dir, "main.go"), []byte(src), 0o644); err != nil {
			t.Fatal(err)
		}
		prog, err := loadProgram(dir, sup)
		if err != nil {
			t.Fatal(err)
		}
		prog.census()
		n := map[string]int{}
		for _, d := range prog.pkgs["main"].decls {
			for _, f := range d.Findings {
				switch f.Cause.ID {
				case "compiler-directive", "runtime-setting":
					if !f.Certain || !f.Export || f.Cause.Scope != "export" {
						t.Fatalf("%s must be certain and export-scoped: %+v", f.Cause.ID, f)
					}
					n[f.Cause.ID]++
				}
			}
		}
		return n
	}
	cases := []struct {
		label, src string
		want       map[string]int
	}{
		{"go:embed", "package main\n\nimport _ \"embed\"\n\n//go:embed data.txt\nvar x string\n\nfunc main() { println(len(x)) }\n", map[string]int{"compiler-directive": 1}},
		{"go:linkname in a body-less declaration", "package main\n\nimport _ \"unsafe\"\n\n//go:linkname f\nfunc f()\n\nfunc main() {}\n", map[string]int{"compiler-directive": 1}},
		{"go:debug before the package clause", "//go:debug panicnil=1\npackage main\n\nfunc main() {}\n", map[string]int{"runtime-setting": 1}},
		{"//line at column 1 and /*line*/ inline", "package main\n\n//line other.go:10\nfunc main() { /*line other.go:20*/ println(1) }\n", map[string]int{"compiler-directive": 2}},
		{"indented //go:nosplit inside a body", "package main\n\nfunc main() {\n\t//go:nosplit\n\tprintln(1)\n}\n", map[string]int{"compiler-directive": 1}},
		{"the allowlist and prose", "//go:build !with_tla\n\npackage main\n\n//go:generate echo hi\n//go:noinline\nfunc f() { println(1) }\n\n// go:embed with a blank is prose; so is //golang:\n//golang: x\nfunc main() { f() }\n", map[string]int{}},
	}
	for _, c := range cases {
		t.Run(c.label, func(t *testing.T) {
			got := count(t, c.src)
			for id, n := range c.want {
				if got[id] != n {
					t.Fatalf("want %d %s finding(s), got %d (all: %v)", n, id, got[id], got)
				}
			}
			for id, n := range got {
				if c.want[id] != n {
					t.Fatalf("unexpected %s findings: %d (all: %v)", id, n, got)
				}
			}
		})
	}
	// The dynamic pass: the frontend's four refusal texts classify to the
	// two causes (the go.mod text must NOT fall to foreign-module-version,
	// whose `module directive:` pattern follows in table order).
	texts := map[string]string{
		"nativefrontend: native frontend unsupported: file selection in /x: main.go:5:1 carries the compiler directive `//go:embed data.txt` — a //go: directive outside the allowlist (//go:build, //go:noinline, //go:generate) is not modeled": "compiler-directive",
		"nativefrontend: native frontend unsupported: file selection in /x: main.go:3:1 carries the line directive `//line other.go:100` — position rewriting is not modeled":                                                                     "compiler-directive",
		"nativefrontend: native frontend unsupported: file selection in /x: main.go:1:1 carries the runtime-setting directive `//go:debug panicnil=1` — GODEBUG settings are not modeled":                                                         "runtime-setting",
		"nativefrontend: native frontend unsupported: module directive: /x/go.mod sets godebug (godebug panicnil=1) — GODEBUG settings are not modeled":                                                                                           "runtime-setting",
	}
	for text, want := range texts {
		c, _ := classifyText(text)
		if c == nil || c.ID != want {
			t.Fatalf("%q must classify as %s, got %+v", text, want, c)
		}
	}
	// The allowlist is the ruled set, spelled the same as the frontend's.
	if len(allowedDirectiveVerbs) != 3 || !allowedDirectiveVerbs["go:build"] || !allowedDirectiveVerbs["go:noinline"] || !allowedDirectiveVerbs["go:generate"] {
		t.Fatalf("allowlist drifted from the frontend's: %v", allowedDirectiveVerbs)
	}
}
