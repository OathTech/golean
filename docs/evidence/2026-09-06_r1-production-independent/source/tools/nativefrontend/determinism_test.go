package main

// BUG-091 guard (2026-09-04, lane fr22-fr23 on the hygiene-a-series
// finding): the emitter's OUTPUT — the wire bytes, or the refusal text
// when it refuses — must be a function of the source alone. A `for … :=
// range <map>` whose iteration order reaches an emitted string or wire
// field makes the wire nondeterministic across runs (measured on main
// before the fix: a 2-label goto program refused naming "next" 26 times
// and "fallback" 4 times out of 30). This test emits a fixed set of
// programs N times and asserts byte-identical output; it was RED on
// main's emitter for the goto shape (docs/evidence/2026-09-04_fr22-fr23/
// bug091-red-first.txt) and is the bug's standing guard.

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// The 2-label goto shape: both labels are goto targets NOT at the
// function body's top level (inside the `if`), so the refusal loop over
// e.gotoLabels names one of them — whichever the map yields first.
const detGotoSrc = `package main

func f(n int) int {
	if n > 0 {
	next:
		n--
		if n > 3 {
			goto next
		}
	fallback:
		n += 2
		if n < 0 {
			goto fallback
		}
	}
	return n
}

func main() { println(f(5)) }
`

// A multi-quarantine shape that EXPORTS (audit fix round item 2: the
// first cut carried a complex128 method whose signature refused the whole
// export, making the case one constant string 20× — vacuous): opaque
// generic stubs, an interface with an opaque requirement, poisoned
// package-level vars (`$poisoned` cells), imported method-set stubs,
// promotion wrappers — every table the emitter sorts or should sort
// (70 stubs + 5 `$poisoned` cells on the current emitter).
const detMultiSrc = `package main

import (
	"iter"
	"os"
	"time"
)

type Bag struct{ items []int }

func (b Bag) All() iter.Seq[int] {
	return func(yield func(int) bool) {
		for _, v := range b.items {
			if !yield(v) {
				return
			}
		}
	}
}

type Iterable interface{ All() iter.Seq[int] }

type Outer struct {
	Bag
	tag string
}

var env = os.Getenv("GOLEAN_NEVER_SET")
var when = time.Date(2020, 1, 1, 0, 0, 0, 0, time.UTC)
var later = when

func useEnv() int   { return len(env) }
func useLater() bool { return later.IsZero() }
func useOuter() bool {
	_, ok := any(Outer{tag: "x"}).(Iterable)
	return ok
}

func main() { println(useEnv(), useLater(), useOuter()) }
`

// emitOnce returns the canonical bytes of one emission: the wire as JSON,
// or the refusal text.
func emitOnce(t *testing.T, src string) string {
	t.Helper()
	program, err := emitSource(t, src)
	if err != nil {
		return "REFUSED: " + err.Error()
	}
	b, jerr := json.Marshal(program)
	if jerr != nil {
		t.Fatalf("marshal: %v", jerr)
	}
	return string(b)
}

func TestEmitIsDeterministic(t *testing.T) {
	const runs = 20
	for _, tc := range []struct{ name, src string }{
		{"goto-two-labels", detGotoSrc},
		{"multi-quarantine", detMultiSrc},
	} {
		first := emitOnce(t, tc.src)
		for i := 1; i < runs; i++ {
			if got := emitOnce(t, tc.src); got != first {
				t.Fatalf("%s: emission %d differs from emission 0 (BUG-091: a map iteration order reached the output)\n--- 0:\n%.400s\n--- %d:\n%.400s", tc.name, i, first, i, got)
			}
		}
	}
	// The goto shape lands as a per-declaration STUB whose refusal text
	// names a label; it must be the alphabetically-first one — the
	// sorted order, not the map's (this is the byte that flipped on main).
	if got := emitOnce(t, detGotoSrc); !strings.Contains(got, `"goto target label fallback not at function body top level"`) {
		t.Fatalf("goto shape: stub does not name the sorted-first label: %.400s", got)
	}
}

// The multi-quarantine shape must actually EXPORT, with the tables the
// case exists to guard present — otherwise the byte comparison above is
// comparing one refusal string with itself.
func TestDeterminismShapeExports(t *testing.T) {
	program, err := emitSource(t, detMultiSrc)
	if err != nil {
		t.Fatalf("multi-quarantine shape must export (a whole-export refusal makes the determinism case vacuous): %v", err)
	}
	stubs := 0
	for _, key := range []string{"funcs", "methods"} {
		for _, x := range program[key].([]any) {
			if m, ok := x.(map[string]any); ok && m["unsupported"] != nil {
				stubs++
			}
		}
	}
	poisoned := 0
	for _, g := range program["globals"].([]any) {
		if namedTypeName(g.(map[string]any)["type"]) == poisonedCellTypeId {
			poisoned++
		}
	}
	if stubs < 10 || poisoned != 3 {
		t.Fatalf("shape carries %d stubs and %d $poisoned cells; want many stubs (>= 10) and exactly 3 poisoned (env, when, later)", stubs, poisoned)
	}
}

// UNITS-BEARING determinism (audit fix round item 2): emitSource type-checks
// with importer.Default and never builds source units, so the sorted
// refusal sites in the LOADER path — langversion.go's reserved-tag scan
// (load.go's per-unit constraint check) and stdlibreach.go's library
// scans — are unreachable from the cases above. These run the REAL
// pipeline (lowerProgramDir: parse → shims → loadProgram → emitProgram).
func TestEmitIsDeterministicWithUnits(t *testing.T) {
	withStdlibRoots(t)
	const runs = 12
	// (a) a case-local package whose one file carries a build constraint
	// naming TWO reserved tags: the refusal must name the sorted-first
	// tag (`darwin`), never `linux` — the langversion.go:178 site.
	dir := writeMain(t, `package main

import "helper"

func main() { println(helper.N) }
`)
	if err := os.MkdirAll(filepath.Join(dir, "helper"), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "helper", "h.go"), []byte("//go:build linux || darwin\n\npackage helper\n\nconst N = 1\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	var first string
	for i := 0; i < runs; i++ {
		_, err := lowerProgramDir(t, dir)
		if err == nil {
			t.Fatalf("a reserved-tag build constraint must refuse the export")
		}
		if i == 0 {
			first = err.Error()
			if !strings.Contains(first, `reserved tag "darwin"`) {
				t.Fatalf("refusal must name the sorted-first reserved tag darwin: %s", first)
			}
			continue
		}
		if err.Error() != first {
			t.Fatalf("units-bearing refusal text differs between runs (BUG-091):\n%s\n%s", first, err.Error())
		}
	}
	// (b) a program through two source-through library units (strings,
	// errors): the loader, reach walk and library pruning must yield
	// byte-identical wires.
	lib := writeMain(t, `package main

import (
	"errors"
	"strings"
)

var banner = strings.Repeat("ab", 3)
var sentinel = errors.New("boom")

func f() string { return banner + sentinel.Error() }

func main() { println(f()) }
`)
	var firstWire string
	for i := 0; i < 6; i++ {
		program, err := lowerProgramDir(t, lib)
		if err != nil {
			t.Fatalf("library program must export: %v", err)
		}
		b, jerr := json.Marshal(program)
		if jerr != nil {
			t.Fatal(jerr)
		}
		if i == 0 {
			firstWire = string(b)
			continue
		}
		if string(b) != firstWire {
			t.Fatalf("units-bearing wire differs between runs %d and 0 (BUG-091)", i)
		}
	}
}
