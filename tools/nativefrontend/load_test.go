package main

import (
	"fmt"
	"go/token"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// cmd/go's import rules on case-local imports (load.go judgeLocalImport /
// judgeLocalUnit, BUG-219), each cell measured against gc go1.26.5 on
// 2026-10-27 under the runners' environments (the lane's probes g1–g14 in
// GOPATH mode, m1–m14 and the S20 sweep's m-batch in module mode). A
// refusal here is the `type-check` rejection class with gc's reason; an
// `unsupported` is the frontend's own fail-closed refusal of a shape gc
// builds differently; "" is acceptance on both sides.
func TestLocalImportRules(t *testing.T) {
	withStdlibRoots(t)
	mainOf := func(path string) string {
		return fmt.Sprintf("package main\n\nimport x %q\n\nfunc probe() int { return x.F() }\n\nfunc main() { println(probe()) }\n", path)
	}
	lib := func(name string) string { return "package " + name + "\n\nfunc F() int { return 1 }\n" }
	type tc struct {
		name  string
		files map[string]string // relative path -> content
		want  string            // "" = accepted; "type-check: " + gc's text; or an unsupported substring
	}
	gomod := "module test\n\ngo 1.26\n"
	cases := []tc{
		// GOPATH mode
		{"gopath vendor element", map[string]string{"main.go": mainOf("vendor/lib"), "vendor/lib/p.go": lib("lib")},
			"type-check: main.go:3:8: use of vendored package not allowed"},
		{"gopath nested vendor element", map[string]string{"main.go": mainOf("lib/vendor/x"), "lib/vendor/x/p.go": lib("x")},
			"type-check: main.go:3:8: use of vendored package not allowed"},
		{"gopath terminating vendor is its own package but shadowed by GOROOT/src/vendor", map[string]string{"main.go": mainOf("vendor"), "vendor/p.go": lib("vendor")},
			"type-check: main.go:3:8: import \"vendor\": no Go files in GOROOT/src/vendor"},
		{"gopath lib/vendor terminating: its own package, accepted", map[string]string{"main.go": mainOf("lib/vendor"), "lib/vendor/p.go": lib("vendor")}, ""},
		{"gopath internal from main", map[string]string{"main.go": mainOf("internal/x"), "internal/x/p.go": lib("x")},
			"type-check: main.go:3:8: use of internal package internal/x not allowed"},
		{"gopath nested internal from main", map[string]string{"main.go": mainOf("lib/internal/x"), "lib/internal/x/p.go": lib("x")},
			"type-check: main.go:3:8: use of internal package lib/internal/x not allowed"},
		{"gopath internal suffix from main", map[string]string{"main.go": mainOf("lib/internal"), "lib/internal/p.go": lib("internal")},
			"type-check: main.go:3:8: use of internal package lib/internal not allowed"},
		{"gopath bare internal: shadowed by GOROOT/src/internal", map[string]string{"main.go": mainOf("internal"), "internal/p.go": lib("internal")},
			"type-check: main.go:3:8: import \"internal\": no Go files in GOROOT/src/internal"},
		{"gopath lib imports its own internal: accepted", map[string]string{"main.go": mainOf("lib"),
			"lib/p.go": "package lib\n\nimport \"lib/internal/x\"\n\nfunc F() int { return x.G() }\n", "lib/internal/x/p.go": "package x\n\nfunc G() int { return 1 }\n"}, ""},
		{"gopath a imports b's internal", map[string]string{"main.go": mainOf("a"),
			"a/p.go": "package a\n\nimport \"b/internal/x\"\n\nfunc F() int { return x.G() }\n", "b/internal/x/p.go": "package x\n\nfunc G() int { return 1 }\n"},
			"type-check: a/p.go:3:8: use of internal package b/internal/x not allowed"},
		{"gopath main imports lib's internal that lib itself imports (every edge is judged)", map[string]string{
			"main.go": "package main\n\nimport (\n\tx \"lib\"\n\ty \"lib/internal/x\"\n)\n\nfunc probe() int { return x.F() + y.G() }\n\nfunc main() { println(probe()) }\n",
			"lib/p.go": "package lib\n\nimport \"lib/internal/x\"\n\nfunc F() int { return x.G() }\n", "lib/internal/x/p.go": "package x\n\nfunc G() int { return 1 }\n"},
			"type-check: main.go:5:2: use of internal package lib/internal/x not allowed"},
		{"gopath package main, aliased", map[string]string{"main.go": mainOf("prog"), "prog/p.go": "package main\n\nfunc F() int { return 1 }\n\nfunc main() {}\n"},
			"type-check: main.go:3:8: import \"prog\" is a program, not an importable package"},
		{"gopath package main through a local package", map[string]string{"main.go": mainOf("lib"),
			"lib/p.go": "package lib\n\nimport p \"prog\"\n\nfunc F() int { return p.F() }\n", "prog/p.go": "package main\n\nfunc F() int { return 1 }\n\nfunc main() {}\n"},
			"type-check: lib/p.go:3:8: import \"prog\" is a program, not an importable package"},
		{"gopath _lib: accepted", map[string]string{"main.go": mainOf("_lib"), "_lib/p.go": lib("lib")}, ""},
		{"gopath testdata/lib: accepted", map[string]string{"main.go": mainOf("testdata/lib"), "testdata/lib/p.go": lib("lib")}, ""},
		// module mode
		{"module vendor element", map[string]string{"go.mod": gomod, "main.go": mainOf("vendor/lib"), "vendor/lib/p.go": lib("lib")},
			"type-check: main.go:3:8: vendor/lib must be imported as lib"},
		{"module nested vendor element", map[string]string{"go.mod": gomod, "main.go": mainOf("lib/vendor/x"), "lib/vendor/x/p.go": lib("x")},
			"type-check: main.go:3:8: lib/vendor/x must be imported as x"},
		{"module terminating vendor: not in std", map[string]string{"go.mod": gomod, "main.go": mainOf("vendor"), "vendor/p.go": lib("vendor")},
			"type-check: main.go:3:8: package vendor is not in std"},
		{"module bare internal path: not in std", map[string]string{"go.mod": gomod, "main.go": mainOf("internal/x"), "internal/x/p.go": lib("x")},
			"type-check: main.go:3:8: package internal/x is not in std"},
		{"module bare local path: not in std", map[string]string{"go.mod": gomod, "main.go": mainOf("lib"), "lib/p.go": lib("lib")},
			"type-check: main.go:3:8: package lib is not in std"},
		{"module dotted local path: no required module", map[string]string{"go.mod": gomod, "main.go": mainOf("a.b/lib"), "a.b/lib/p.go": lib("lib")},
			"type-check: main.go:3:8: no required module provides package a.b/lib"},
		{"module require+replace control: accepted", map[string]string{"go.mod": gomod + "\nrequire lib v0.0.0\n\nreplace lib => ./lib\n", "main.go": mainOf("lib"), "lib/p.go": lib("lib"), "lib/go.mod": "module lib\n\ngo 1.26\n"}, ""},
		{"module versioned replace: accepted", map[string]string{"go.mod": gomod + "\nrequire lib v1.2.3\n\nreplace lib v1.2.3 => ./lib\n", "main.go": mainOf("lib"), "lib/p.go": lib("lib"), "lib/go.mod": "module lib\n\ngo 1.26\n"}, ""},
		{"module replace without require", map[string]string{"go.mod": gomod + "\nreplace lib => ./lib\n", "main.go": mainOf("lib"), "lib/p.go": lib("lib"), "lib/go.mod": "module lib\n\ngo 1.26\n"},
			"type-check: main.go:3:8: module lib provides package lib and is replaced but not required"},
		{"module require without replace", map[string]string{"go.mod": gomod + "\nrequire lib v0.0.0\n", "main.go": mainOf("lib"), "lib/p.go": lib("lib"), "lib/go.mod": "module lib\n\ngo 1.26\n"},
			"type-check: main.go:3:8: missing go.sum entry for module providing package lib"},
		{"module replacement without a go.mod", map[string]string{"go.mod": gomod + "\nrequire lib v0.0.0\n\nreplace lib => ./lib\n", "main.go": mainOf("lib"), "lib/p.go": lib("lib")},
			"type-check: main.go:3:8: module ./lib: reading lib/go.mod: no such file or directory"},
		{"module replace onto another directory: refused by name", map[string]string{"go.mod": gomod + "\nrequire lib v0.0.0\n\nreplace lib => ./other\n", "main.go": mainOf("lib"), "lib/p.go": lib("lib"), "lib/go.mod": "module lib\n\ngo 1.26\n", "other/p.go": lib("lib"), "other/go.mod": "module lib\n\ngo 1.26\n"},
			"which is not the case-local directory"},
		{"module vendor directory beside a replaced import: refused by name", map[string]string{"go.mod": gomod + "\nrequire lib v0.0.0\n\nreplace lib => ./lib\n", "main.go": mainOf("lib"), "lib/p.go": lib("lib"), "lib/go.mod": "module lib\n\ngo 1.26\n", "vendor/stray.txt": "x\n"},
			"module directive: "},
		{"module replace-backed internal/x: accepted (the empty parent)", map[string]string{"go.mod": gomod + "\nrequire internal/x v0.0.0\n\nreplace internal/x => ./internal/x\n", "main.go": mainOf("internal/x"), "internal/x/p.go": lib("x"), "internal/x/go.mod": "module internal/x\n\ngo 1.26\n"}, ""},
		{"module replace-backed lib/internal/x from test: not allowed", map[string]string{"go.mod": gomod + "\nrequire lib/internal/x v0.0.0\n\nreplace lib/internal/x => ./lib/internal/x\n", "main.go": mainOf("lib/internal/x"), "lib/internal/x/p.go": lib("x"), "lib/internal/x/go.mod": "module lib/internal/x\n\ngo 1.26\n"},
			"type-check: main.go:3:8: use of internal package lib/internal/x not allowed"},
		{"module package main, aliased, replace-backed", map[string]string{"go.mod": gomod + "\nrequire prog v0.0.0\n\nreplace prog => ./prog\n", "main.go": mainOf("prog"), "prog/p.go": "package main\n\nfunc F() int { return 1 }\n\nfunc main() {}\n", "prog/go.mod": "module prog\n\ngo 1.26\n"},
			"type-check: main.go:3:8: import \"prog\" is a program, not an importable package"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			dir := t.TempDir()
			for rel, content := range c.files {
				path := filepath.Join(dir, filepath.FromSlash(rel))
				if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
					t.Fatal(err)
				}
				if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
					t.Fatal(err)
				}
			}
			fset := token.NewFileSet()
			files, err := selectPackageFiles(fset, dir)
			if err != nil {
				t.Fatalf("select: %v", err)
			}
			_, err = loadProgram(fset, dir, files)
			if c.want == "" {
				if err != nil {
					t.Fatalf("want acceptance, got %v", err)
				}
				return
			}
			if err == nil {
				t.Fatalf("want a refusal containing %q, got acceptance", c.want)
			}
			// Positions carry the temp dir: compare with it stripped.
			got := strings.ReplaceAll(err.Error(), dir+string(os.PathSeparator), "")
			if !strings.Contains(got, c.want) {
				t.Fatalf("refusal %q does not contain %q", got, c.want)
			}
			if strings.HasPrefix(c.want, "type-check: ") && strings.Contains(got, "could not import") {
				t.Fatalf("a type-check-class refusal must not read as an importer failure: %q", got)
			}
		})
	}
}
