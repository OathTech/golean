package main

import (
	"go/token"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// The entry rule (entrymode.go, BUG-125): by default a `package main`
// with no `func main` refuses as a type-check-class rejection with gc's
// text; --subject skips it; a package that declares main and a library
// package are unaffected in both modes.
func TestEntryDeclaredRule(t *testing.T) {
	load := func(t *testing.T, src string) error {
		t.Helper()
		dir := t.TempDir()
		if err := os.WriteFile(filepath.Join(dir, "main.go"), []byte(src), 0o644); err != nil {
			t.Fatal(err)
		}
		fset := token.NewFileSet()
		files, err := selectPackageFiles(fset, dir)
		if err != nil {
			t.Fatal(err)
		}
		_, err = loadProgram(fset, dir, files)
		return err
	}
	cases := []struct {
		name, src       string
		refuseByDefault bool
	}{
		{"no-main", "package main\n\nfunc f() int { return 1 }\n", true},
		{"with-main", "package main\n\nfunc f() int { return 1 }\n\nfunc main() { _ = f() }\n", false},
		{"method-named-main", "package main\n\ntype T struct{}\n\nfunc (T) main() {}\n", true},
		{"library", "package lib\n\nfunc F() int { return 1 }\n", false},
	}
	defer func(saved bool) { subjectMode = saved }(subjectMode)
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			subjectMode = false
			err := load(t, c.src)
			if c.refuseByDefault {
				if err == nil || !strings.HasPrefix(err.Error(), "type-check: function main is undeclared in the main package") {
					t.Fatalf("default mode: want gc's type-check-class refusal, got %v", err)
				}
			} else if err != nil {
				t.Fatalf("default mode: want acceptance, got %v", err)
			}
			subjectMode = true
			if err := load(t, c.src); err != nil {
				t.Fatalf("--subject: want acceptance, got %v", err)
			}
		})
	}
}

// The reference rule (entrymode.go, BUG-220; row 41's ruling: main stays
// unexported): a reference to the main package's `main` from outside its
// own body refuses by name in both modes; a method, a local, a recursive
// main and an imported package's `main` are not references to it.
func TestEntryReferencedRule(t *testing.T) {
	load := func(t *testing.T, files map[string]string) error {
		t.Helper()
		dir := t.TempDir()
		for rel, src := range files {
			path := filepath.Join(dir, filepath.FromSlash(rel))
			if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
				t.Fatal(err)
			}
			if err := os.WriteFile(path, []byte(src), 0o644); err != nil {
				t.Fatal(err)
			}
		}
		fset := token.NewFileSet()
		files2, err := selectPackageFiles(fset, dir)
		if err != nil {
			t.Fatal(err)
		}
		_, err = loadProgram(fset, dir, files2)
		return err
	}
	one := func(src string) map[string]string { return map[string]string{"main.go": src} }
	cases := []struct {
		name   string
		files  map[string]string
		refuse bool
	}{
		{"call", one("package main\n\nvar n int\n\nfunc main() { n++ }\nfunc probe() int { main(); return n }\n"), true},
		{"func value", one("package main\n\nvar n int\n\nfunc main() { n++ }\nfunc probe() int { f := main; f(); return n }\n"), true},
		{"deferred", one("package main\n\nvar n int\n\nfunc main() { n++ }\nfunc probe() int { defer main(); return n }\n"), true},
		{"go statement", one("package main\n\nvar n int\n\nfunc main() { n++ }\nfunc probe() int { go main(); return n }\n"), true},
		{"closure in another function", one("package main\n\nvar n int\n\nfunc main() { n++ }\nfunc probe() int { g := func() { main() }; g(); return n }\n"), true},
		{"init", one("package main\n\nvar n int\n\nfunc init() { if n == 0 { n++; main() } }\nfunc main() { n++ }\nfunc probe() int { return n }\n"), true},
		{"dead code still references it", one("package main\n\nfunc main() {}\nfunc probe() int { if false { main() }; return 7 }\n"), true},
		{"method value in another file", map[string]string{"main.go": "package main\n\nfunc main() {}\n", "b.go": "package main\n\nfunc probe() int { f := main; _ = f; return 1 }\n"}, true},
		{"recursive main: inside its own body", one("package main\n\nvar n int\n\nfunc main() { if n == 0 { n++; main() } }\nfunc probe() int { return n }\n"), false},
		{"method named main", one("package main\n\ntype T struct{}\n\nfunc (T) main() int { return 1 }\nfunc probe() int { return T{}.main() }\nfunc main() { println(probe()) }\n"), false},
		{"local named main", one("package main\n\nfunc probe() int { main := 5; return main }\nfunc main() { println(probe()) }\n"), false},
		{"an imported package's main is an ordinary function", map[string]string{
			"main.go": "package main\n\nimport \"lib\"\n\nfunc probe() int { return lib.F() }\nfunc main() { println(probe()) }\n",
			"lib/p.go": "package lib\n\nfunc main() int { return 1 }\n\nfunc F() int { return main() }\n"}, false},
	}
	defer func(saved bool) { subjectMode = saved }(subjectMode)
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			for _, subject := range []bool{false, true} {
				subjectMode = subject
				err := load(t, c.files)
				if c.refuse {
					if err == nil || !strings.Contains(err.Error(), "function main is referenced at") {
						t.Fatalf("subject=%v: want the BUG-220 refusal by name, got %v", subject, err)
					}
				} else if err != nil {
					t.Fatalf("subject=%v: want acceptance, got %v", subject, err)
				}
			}
		})
	}
}
