package main

// FR-36 (2026-10-06, dotimport.go): a DOT import of a stdlib package reaches
// the SAME object-keyed binding as the selector spelling — the primitive
// lowers, the quarantined member refuses BY NAME (import form named), the
// source-through member lowers as a qualified call, and the value shape
// refuses on FR-14's line. Before: a bare user `call` and a runtime `stuck`.
// A refusal inside a declaration is the standing PER-DECLARATION quarantine
// (the export succeeds; the declaration becomes an `unsupported` stub that
// refuses when CALLED, and diff-coverage classifies the called stub as the
// `frontend-export` stage), so the refusal tests read the stub's reason.

import (
	"strings"
	"testing"
)

// stubReason returns the per-declaration quarantine reason of `name`, or ""
// when the declaration lowered with a body.
func stubReason(t *testing.T, program map[string]any, name string) string {
	t.Helper()
	fn, ok := funcNames(program)[name]
	if !ok {
		t.Fatalf("declaration %s is missing from the wire", name)
	}
	reason, _ := fn["unsupported"].(string)
	return reason
}

func TestDotImportRandIntnLowersToPrimitive(t *testing.T) {
	src := `package main
import . "math/rand"
func subject() int {
	return Intn(5)
}
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("a dot-imported math/rand.Intn call must lower like the qualified spelling (FR-36): %v", err)
	}
	if reason := stubReason(t, program, "subject"); reason != "" {
		t.Fatalf("a dot-imported Intn(5) must not be quarantined: %s", reason)
	}
	msg := mustJSON(t, program)
	if !strings.Contains(msg, `"expr":"rand-intn"`) || !strings.Contains(msg, `"callee":"Intn"`) {
		t.Errorf("a dot-imported Intn(5) must lower to the rand-intn primitive with callee tag Intn:\n%s", msg)
	}
	if strings.Contains(msg, `"func":"Intn"`) {
		t.Errorf("a dot-imported Intn(5) must not lower as a bare user call (the pre-FR-36 defect):\n%s", msg)
	}
}

func TestDotImportQuarantinedMemberRefusesByName(t *testing.T) {
	src := `package main
import . "math/rand"
func subject() int {
	return len(Perm(3))
}
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("the per-declaration quarantine keeps the export OK: %v", err)
	}
	reason := stubReason(t, program, "subject")
	if reason == "" {
		t.Fatalf("a dot-imported quarantined member (math/rand.Perm) must quarantine the declaration, not lower as a bare user call:\n%s", mustJSON(t, program))
	}
	for _, want := range []string{`package-selector call rand.Perm`, `package "math/rand" surface not modeled`, `dot import`, `FR-36`} {
		if !strings.Contains(reason, want) {
			t.Errorf("the refusal must carry %q (the selector spelling's own text, the import form named):\n%s", want, reason)
		}
	}
}

func TestDotImportFmtDesugarMemberRefusesNamingDesugar(t *testing.T) {
	src := `package main
import . "fmt"
func subject() string {
	return Sprintf("%d", 7)
}
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("the per-declaration quarantine keeps the export OK: %v", err)
	}
	reason := stubReason(t, program, "subject")
	if reason == "" {
		t.Fatalf("a dot-imported fmt desugar member must quarantine the declaration by name (the desugar lowers the qualified spelling only):\n%s", mustJSON(t, program))
	}
	if !strings.Contains(reason, "dot-imported fmt.Sprintf") || !strings.Contains(reason, "qualified spelling only") {
		t.Errorf("the refusal must name the dot-imported fmt member and the desugar's scope:\n%s", reason)
	}
}

func TestDotImportStdlibFuncValueRefusesOnFR14Line(t *testing.T) {
	for _, src := range []string{
		`package main
import . "math/rand"
func subject() int {
	f := Intn
	return f(5)
}
`,
		`package main
import . "math/rand"
func subject() {
	defer Intn(5)
}
`,
	} {
		program, err := emitSource(t, src)
		if err != nil {
			t.Fatalf("the per-declaration quarantine keeps the export OK: %v", err)
		}
		reason := stubReason(t, program, "subject")
		if reason == "" {
			t.Errorf("a dot-imported stdlib function in value position must quarantine the declaration (the primitives lower at direct-call sites only):\n%s", src)
			continue
		}
		if !strings.Contains(reason, "dot-imported stdlib function rand.Intn") || !strings.Contains(reason, "in value position") {
			t.Errorf("the value-position refusal must name the dot-imported member and the shape:\n%s", reason)
		}
	}
}

// The SOURCE-THROUGH case needs the real loader (the library units): a
// dot-imported `strings.ToUpper` is a source function and lowers as the
// path-qualified call, byte-for-byte the qualified spelling's shape.
func TestDotImportSourceThroughMemberLowersQualified(t *testing.T) {
	withStdlibRoots(t)
	dir := writeMain(t, `package main
import . "strings"
func subject() int {
	return len(ToUpper("ab"))
}
func main() { println(subject()) }
`)
	program, err := lowerProgramDir(t, dir)
	if err != nil {
		t.Fatalf("a dot-imported source-through member must lower (FR-36 keeps it green): %v", err)
	}
	if reason := stubReason(t, program, "subject"); reason != "" {
		t.Fatalf("a dot-imported ToUpper must not be quarantined: %s", reason)
	}
	msg := mustJSON(t, program)
	if !strings.Contains(msg, `"func":"strings.ToUpper"`) {
		t.Errorf("a dot-imported ToUpper must lower as the qualified call strings.ToUpper:\n%s", msg)
	}
}
