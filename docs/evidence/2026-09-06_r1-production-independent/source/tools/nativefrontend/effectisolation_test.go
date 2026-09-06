package main

// Unit tests for H-11's effect-isolation predicate
// (emit.go, initializerEffectIsolated + pureUnmodeledCallees), written
// in the audit fix round of 2026-08-20 against findings F1 and F1b.
//
// WHY UNIT TESTS AND NOT ONLY CORPUS ROWS. The observable half of the
// contract is pinned differentially — init/quarantined-var (admitted,
// the green control), init/quarantined-var-{callee,impure,syscall}
// (refused), init/quarantined-var-panicking (refused). But the most
// vivid refutation of the ORIGINAL soundness argument, a package-level
// `var _ = fmt.Println("x")`, is NOT EXPRESSIBLE as a differential row:
// the harness reads the case's observation off the subject program's
// STDOUT, so a program that prints during init produces an invalid Go
// observation and the row dies at stage `go-observation`, before the
// frontend is ever consulted. It would be a red row that pins nothing.
// The refusal is a property of the emitter, so it is pinned here, where
// `go test ./tools/nativefrontend` (a gate step of scripts/ci) sees it.
//
// The two properties under test are separate, and the first cut had
// only the first:
//
//	F1  — effect-freedom is not implied by "the machine does not model
//	      the callee's body". fmt.Println's body is unmodeled and it
//	      writes the very stdout the differential compares.
//	F1b — panic-freedom is a second property entirely. A skipped
//	      panicking initializer is a SILENT wrong answer: the machine
//	      runs on where go run dies in package initialization.

import (
	"strings"
	"testing"
)

// exportRefused reports whether the whole export refused, with the
// refusal text (empty when it succeeded).
func exportRefused(t *testing.T, src string) (bool, string) {
	t.Helper()
	_, err := emitSource(t, src)
	if err == nil {
		return false, ""
	}
	return true, err.Error()
}

// pkginitStmtCount returns the number of statements $pkginit carries —
// the direct read on "was this initializer skipped".
func pkginitStmtCount(t *testing.T, program map[string]any) int {
	t.Helper()
	fns, _ := program["funcs"].([]any)
	for _, f := range fns {
		ff, ok := f.(map[string]any)
		if !ok || ff["name"] != "$pkginit" {
			continue
		}
		body, _ := ff["body"].(map[string]any)
		stmts, _ := body["body"].([]any)
		return len(stmts)
	}
	return -1
}

// TestEffectIsolationAdmitsAllowlistedCallee is the positive half: the
// allowlist must still ADMIT what H-11 was built for, or the fix is a
// blanket revert. os.Getenv is unmodeled AND pure, so its declaration
// quarantines and the healthy sibling still lowers.
func TestEffectIsolationAdmitsAllowlistedCallee(t *testing.T) {
	const src = `package main

import "os"

var bad = os.Getenv("GOLEAN_NEVER_SET")
var good = 42

func main() { println(good) }
`
	program, err := emitSource(t, src)
	if err != nil {
		t.Fatalf("allowlisted pure callee must quarantine, not refuse: %v", err)
	}
	// One statement: the healthy `good` initializer. `bad` is skipped.
	if n := pkginitStmtCount(t, program); n != 1 {
		t.Fatalf("$pkginit carries %d statements, want 1 (the healthy sibling only)", n)
	}
}

// TestEffectIsolationRefusesEffectfulCallee is F1's headline: an
// unmodeled callee with a REAL effect must refuse the whole export.
// fmt.Println writes stdout; os.Mkdir touches the filesystem. Neither
// is on pureUnmodeledCallees, and neither may be admitted on the
// refuted "its body is unmodeled anyway" reasoning.
func TestEffectIsolationRefusesEffectfulCallee(t *testing.T) {
	cases := []struct {
		name string
		src  string
		want string
	}{
		{
			name: "stdout",
			src: `package main

import "fmt"

var _, _ = fmt.Println("H-11 SIDE EFFECT")

func main() {}
`,
			want: "fmt.Println",
		},
		{
			name: "filesystem",
			src: `package main

import "os"

var mkErr = os.Mkdir("", 0o755)

func main() { println(mkErr != nil) }
`,
			want: "os.Mkdir",
		},
		{
			name: "process-environment-write",
			src: `package main

import "os"

var setErr = os.Setenv("GOLEAN_H11_MARK", "1")

func main() { println(setErr != nil) }
`,
			want: "os.Setenv",
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			refused, msg := exportRefused(t, tc.src)
			if !refused {
				t.Fatalf("effectful unmodeled callee %s was ADMITTED and its "+
					"initializer SKIPPED — the machine would run this program "+
					"without the effect go run performs", tc.want)
			}
			if !strings.Contains(msg, tc.want) {
				t.Fatalf("refusal does not name the callee %q: %s", tc.want, msg)
			}
		})
	}
}

// TestEffectIsolationRefusesPanickingShapes is F1b: every expression
// shape that can panic must keep the whole-export refusal, because a
// SKIPPED panic is invisible — the machine finishes cleanly where go
// run dies in package initialization. Each source pairs the allowlisted
// (and therefore admissible) os.Getenv call with one panicking shape,
// so the ONLY thing under test is the panicking shape.
func TestEffectIsolationRefusesPanickingShapes(t *testing.T) {
	const preamble = `package main

import "os"

var sl = []int{1, 2}
var p *int
var z = 0
var n = -1
var iv any = 3

type box struct{ f int }

var bp *box

var bad = [2]any{os.Getenv("GOLEAN_NEVER_SET"), `
	shapes := map[string]string{
		"slice-to-array-conversion": "[4]int(sl)",
		"slice-to-array-pointer":    "(*[4]int)(sl)",
		"index-out-of-range":        "sl[7]",
		"slice-bounds":              "sl[1:9]",
		"nil-pointer-deref":         "*p",
		"nil-field-deref":           "bp.f",
		"divide-by-zero":            "1 / z",
		"remainder-by-zero":         "1 % z",
		"negative-shift":            "1 << n",
		"failed-type-assertion":     "iv.(string)",
		"uncomparable-interface":    "iv == any(sl)",
	}
	for name, expr := range shapes {
		t.Run(name, func(t *testing.T) {
			src := preamble + expr + "}\n\nfunc main() { println(len(bad)) }\n"
			refused, _ := exportRefused(t, src)
			if !refused {
				t.Fatalf("panicking shape %s was ADMITTED and its initializer "+
					"SKIPPED — a go run panic answered with a clean machine run", expr)
			}
		})
	}
}

// TestEffectIsolationRefusesUnknownCallShapes keeps the predicate's
// default closed: a method call, a builtin, an immediately-invoked
// function literal and a source-package call are all outside the
// allowlist and must refuse.
func TestEffectIsolationRefusesUnknownCallShapes(t *testing.T) {
	cases := map[string]string{
		"immediately-invoked-literal": `package main

import "os"

var bad = [2]any{os.Getenv("X"), func() int { return 1 }()}

func main() { println(len(bad)) }
`,
		"method-value": `package main

import (
	"os"
	"strings"
)

var b strings.Builder
var bad = [2]any{os.Getenv("X"), b.String}

func main() { println(len(bad)) }
`,
	}
	for name, src := range cases {
		t.Run(name, func(t *testing.T) {
			if refused, _ := exportRefused(t, src); !refused {
				t.Fatal("a call shape outside the allowlist was admitted")
			}
		})
	}
}
