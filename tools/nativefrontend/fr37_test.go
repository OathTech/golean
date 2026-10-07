package main

// FR-37 (2026-10-07, dotimport.go): a DOT-imported package-level VARIABLE of
// a non-source (stdlib) package (`import . "os"`; `len(Args)`) refuses BY
// NAME at the frontend in every shape — read, index, range, assignment
// target, index target, address-of, multi-assignment — instead of reaching
// the wire as a bare `{"expr":"ident","local":0,"name":"Args"}` that the
// decoder refused unnamed (B6 c3) and that, being a whole-wire decode
// failure, masked sibling refusals. The refusal is the standing
// per-declaration quarantine (fr36_test.go header).

import (
	"strings"
	"testing"
)

func TestDotImportStdlibVarRefusesByName(t *testing.T) {
	cases := map[string]string{
		"read": `package main
import . "os"
func subject() int {
	return len(Args)
}
`,
		"index": `package main
import . "os"
func subject() string {
	return Args[0]
}
`,
		"range": `package main
import . "os"
func subject() int {
	n := 0
	for range Args {
		n++
	}
	return n
}
`,
		"assign": `package main
import . "os"
func subject() {
	Args = nil
}
`,
		"index-assign": `package main
import . "os"
func subject() {
	Args[0] = "x"
}
`,
		"multi-assign": `package main
import . "os"
func subject() int {
	var n int
	Args, n = nil, 1
	return n
}
`,
		"addr": `package main
import . "os"
func subject() int {
	p := &Args
	return len(*p)
}
`,
		"compare-error-var": `package main
import . "io"
func subject(err error) bool {
	return err == EOF
}
`,
		"unseq-shape": `package main
import . "os"
func subject() int {
	f := func() int { Args[0] = "q"; return 5 }
	g := func(x string, y int) int { return len(x) + y }
	return g(Args[0], f())
}
`,
		"closure-write": `package main
import . "os"
func subject() {
	f := func() { Args = nil }
	f()
}
`,
		"closure": `package main
import . "os"
func subject() int {
	f := func() int { return len(Args) }
	return f()
}
`,
	}
	for name, src := range cases {
		t.Run(name, func(t *testing.T) {
			program, err := emitSource(t, src)
			if err != nil {
				t.Fatalf("the per-declaration quarantine keeps the export OK: %v", err)
			}
			msg := mustJSON(t, program)
			reason := stubReason(t, program, "subject")
			if reason == "" {
				t.Fatalf("a dot-imported stdlib package variable must quarantine the declaration by name (FR-37), not reach the decoder:\n%s", msg)
			}
			for _, want := range []string{"imported package-level variable", "has no seeded cell", "dot import", "FR-37"} {
				if !strings.Contains(reason, want) {
					t.Errorf("the refusal must carry %q:\n%s", want, reason)
				}
			}
			if strings.Contains(msg, `"name":"Args"`) || strings.Contains(msg, `"name":"EOF"`) {
				t.Errorf("the dot-imported variable must not reach the wire as a bare local ident:\n%s", msg)
			}
		})
	}
}

// The masking FR-37 named: a program with a dot-imported variable use in
// one declaration and a qualified quarantined call in a sibling exports OK,
// both declarations quarantined by name (before: one bare ident poisoned the
// whole wire at decode, the os.Exit refusal never reported).
func TestDotImportStdlibVarDoesNotMaskSiblingRefusal(t *testing.T) {
	src := `package main
import (
	"os"
	. "os"
)
func reader() int {
	return len(Args)
}
func exiter() {
	os.Exit(3)
}
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("export must succeed: %v", err)
	}
	if r := stubReason(t, program, "reader"); !strings.Contains(r, "FR-37") {
		t.Errorf("reader must refuse by name (FR-37), got %q", r)
	}
	if r := stubReason(t, program, "exiter"); r == "" {
		t.Errorf("exiter's own refusal must stay visible:\n%s", mustJSON(t, program))
	}
}

// A dot import of a SOURCE-THROUGH stdlib package reaches its package-level
// variables as source globals (`isPackageVar`: the package is a source
// unit), so FR-37's arm never fires there: `ErrRange` reads its seeded cell.
func TestDotImportSourceThroughVarIsSourceGlobal(t *testing.T) {
	withStdlibRoots(t)
	dir := writeMain(t, `package main
import . "strconv"
func subject(err error) bool {
	return err == ErrRange
}
func main() { println(subject(nil)) }
`)
	program, err := lowerProgramDir(t, dir)
	if err != nil {
		t.Fatalf("a dot-imported source-through variable must lower: %v", err)
	}
	if reason := stubReason(t, program, "subject"); reason != "" {
		t.Fatalf("a dot-imported source-through variable must not be quarantined: %s", reason)
	}
	msg := mustJSON(t, program)
	if strings.Contains(msg, `"name":"ErrRange"`) || !strings.Contains(msg, `"expr":"globaladdr"`) {
		t.Errorf("ErrRange must read its seeded cell (globaladdr), never a bare ident:\n%s", msg)
	}
}
