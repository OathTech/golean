package main

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestOracleCopyPreservesSemanticSources(t *testing.T) {
	parent := t.TempDir()
	input := filepath.Join(parent, "input")
	out := filepath.Join(parent, "oracle")
	if err := os.Mkdir(input, 0755); err != nil {
		t.Fatal(err)
	}
	source := []byte("package main\n// fake func main() {\n//line /pretend/runtime/panic.go:879\nfunc main() /* { */ { print(\"ok\") }\n")
	other := []byte("package main\nfunc other() string { return `func main() {` }\n")
	if err := os.WriteFile(filepath.Join(input, "main.go"), source, 0644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(input, "other.go"), other, 0644); err != nil {
		t.Fatal(err)
	}
	if err := copyOraclePackage(input, out); err != nil {
		t.Fatal(err)
	}
	for name, want := range map[string][]byte{"main.go": source, "other.go": other} {
		got, err := os.ReadFile(filepath.Join(input, name))
		if err != nil || !bytes.Equal(got, want) {
			t.Fatalf("semantic source changed: %s/%v", name, err)
		}
	}
	got, err := os.ReadFile(filepath.Join(out, "main.go"))
	if err != nil {
		t.Fatal(err)
	}
	want := bytes.Replace(source, []byte("{ print"), []byte("{\n_goleanSetupCrash(); print"), 1)
	if !bytes.Equal(got, want) {
		t.Fatalf("oracle edits exceed insertion: %q", got)
	}
	got, err = os.ReadFile(filepath.Join(out, "other.go"))
	if err != nil || !bytes.Equal(got, other) {
		t.Fatalf("other oracle source changed: %q/%v", got, err)
	}
	got, err = os.ReadFile(filepath.Join(out, crashHelperName))
	if err != nil || string(got) != crashHelperSource {
		t.Fatalf("hook source missing: %v", err)
	}
	if err := copyOraclePackage(input, out); err == nil {
		t.Fatal("existing oracle directory overwritten")
	}
}

func TestOracleCopyRefusals(t *testing.T) {
	for _, tc := range []struct{ source, cause string }{
		{"package main\nfunc f(){}", "no main"},
		{"package main\nfunc main(){}\nfunc main(){}", "duplicate"},
		{"package main\nfunc main(){_goleanSetupCrash()}\nfunc _goleanSetupCrash(){}", "collision"},
		{"package other\nfunc main(){}", "not main"},
	} {
		parent := t.TempDir()
		input := filepath.Join(parent, "input")
		if err := os.Mkdir(input, 0755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(input, "main.go"), []byte(tc.source), 0644); err != nil {
			t.Fatal(err)
		}
		if err := copyOraclePackage(input, filepath.Join(parent, "oracle")); err == nil || !strings.Contains(err.Error(), tc.cause) {
			t.Fatalf("bad source accepted: %v", err)
		}
	}
}
