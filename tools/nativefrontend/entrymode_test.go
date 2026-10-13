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
