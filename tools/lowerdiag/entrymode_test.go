package main

import (
	"os"
	"path/filepath"
	"testing"
)

// The static judge's entry rule matches the frontend's (entrymode.go,
// BUG-125): without --subject a main-less `package main` carries one
// certain, export-scoped main-undeclared finding; with --subject, or
// when func main is declared, none. The dynamic pass classifies the
// frontend's refusal text to the same cause.
func TestEntryDeclaredParity(t *testing.T) {
	if err := initCauses(); err != nil {
		t.Fatal(err)
	}
	sup, err := newSupply("../../docs/stdlib-admission-register.md")
	if err != nil {
		t.Fatal(err)
	}
	count := func(t *testing.T, src string) int {
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
		n := 0
		for _, d := range prog.pkgs["main"].decls {
			for _, f := range d.Findings {
				if f.Cause.ID == "main-undeclared" {
					if !f.Certain || !f.Export || f.Cause.Scope != "export" {
						t.Fatalf("main-undeclared must be certain and export-scoped: %+v", f)
					}
					n++
				}
			}
		}
		return n
	}
	defer func(saved bool) { subjectMode = saved }(subjectMode)
	noMain := "package main\n\nfunc f() int { return 1 }\n"
	withMain := "package main\n\nfunc main() {}\n"
	subjectMode = false
	if n := count(t, noMain); n != 1 {
		t.Fatalf("default: want 1 main-undeclared finding, got %d", n)
	}
	if n := count(t, withMain); n != 0 {
		t.Fatalf("default with func main: want 0, got %d", n)
	}
	subjectMode = true
	if n := count(t, noMain); n != 0 {
		t.Fatalf("--subject: want 0, got %d", n)
	}
	c, _ := classifyText("nativefrontend: type-check: function main is undeclared in the main package (x; gc reports this at link time)")
	if c == nil || c.ID != "main-undeclared" {
		t.Fatalf("the frontend's refusal must classify as main-undeclared, got %+v", c)
	}
}
